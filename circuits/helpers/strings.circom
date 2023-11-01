pragma circom 2.1.3;

include "../../node_modules/circomlib/circuits/comparators.circom";
include "../../node_modules/circomlib/circuits/mux4.circom";
include "../../node_modules/circomlib/circuits/gates.circom";
include "misc.circom";
include "base64.circom";

/**
SliceFixed: Returns a fixed-length slice of an array.
More precisely, in[index:index+outLen] (both inclusive).

Cost: inLen + outLen * inLen

Range checks:
    - index in [0, inLen)
    - index + outLen in [0, inLen]
    - outLen > 0

SliceFixed(inLen, outLen)(in, index)
**/
template SliceFixed(inLen, outLen) {
    assert(outLen > 0);

    signal input in[inLen];
    signal input index;
    signal output out[outLen];

    RangeCheck(numBits(inLen), inLen - 1)(index); // index in [0, inLen - 1]
    RangeCheck(numBits(inLen), inLen)(index + outLen); // index + outLen in [0, inLen]

    // eqs[index] = 1, 0 otherwise
    signal eqs[inLen] <== OneBitVector(inLen)(index);
    for(var i = 0; i < outLen; i++) {
        // arr[i + index] = 1 (if i + index < inLen), 0 otherwise
        var arr[inLen];
        for (var j = 0; j < inLen; j++) {
            if (j < i) {
                arr[j] = 0;
            } else {
                // 这个操作有点骚。
                //   - j是in的下标，i是out的下标。
                //   - 每次i循环里，只有j=i+index时，arr[j]才会被赋值为1。
                //   - 被赋值的arr[j]，与i一样同样是在往前走的。
                arr[j] = eqs[j - i];
            }
        }
        // 标量乘法：
        // EscalarProduct(inLen)(arr, in) = arr_0 * in_0 + arr_1 * in_1 + ...
        // 每次i循环里，arr里只有一个元素是1，因此out[i]就是这个元素的值。
        out[i] <== EscalarProduct(inLen)(arr, in);
    }
}

/**
Slice: Returns a variable-length slice of an array.
More precisely, in[index:index+length] + [0] * (outLen - length).

Cost: Roughly (inLen + outLen + outLen * inLen)

Range checks:
    - index in [0, inLen)
    - length in (0, outLen]
    - index + length in [0, inLen]
    - outLen > 0

此处variable-length的意思：截取的长度作为变量输入，与输出数组的长度不同。对比：
- SliceFixed(inLen, outLen)(in, index)：返回的数组，长度是outLen，截取的是in[index:index+outLen]。
- Slice(inLen, outLen)(in, index, length)：返回的数组，长度是outLen，但截取的是in[index:index+length]。length要小于outLen，多余的位置会被填充为0。
**/
template Slice(inLen, outLen) {
    assert(outLen > 0);

    signal input in[inLen];
    signal input index;
    signal input length;

    RangeCheck(numBits(inLen), inLen - 1)(index); // index in [0, inLen - 1]
    RangeCheck(numBits(outLen), outLen - 1)(length - 1); // length in [1, outLen]
    RangeCheck(numBits(inLen), inLen)(index + length); // index + length in [0, inLen]

    signal output out[outLen];

    // eqs[i] = 1 if i = index, 0 otherwise
    signal eqs[inLen] <== OneBitVector(inLen)(index);
    // lt[i] = 1 if i < length, 0 otherwise
    signal lts[outLen] <== LTBitVector(outLen)(length);

    signal tmp[outLen];
    for(var i = 0; i < outLen; i++) {
        var arr[inLen];
        for (var j = 0; j < inLen; j++) {
            if (j < i) {
                arr[j] = 0;
            } else {
                arr[j] = eqs[j - i];
            }
        }
        tmp[i] <== EscalarProduct(inLen)(arr, in);
        out[i] <== tmp[i] * lts[i];
    }
}

/**
SliceFromStart: Returns a variable-length slice of an array starting from the beginning.
More precisely, in[0:length] + [0] * (outLen - length).

Cost: Very close to 2 * outLen

Range checks:
    - length in (0, outLen]
    - inLen > 0
    - outLen in (0, inLen]
**/
template SliceFromStart(inLen, outLen) {
    assert (outLen > 0);
    assert (outLen <= inLen);

    signal input in[inLen];
    signal input length;

    RangeCheck(numBits(outLen), outLen - 1)(length - 1); // length in [1, outLen]

    signal output out[outLen];

    // lt[i] = 1 if i < length, 0 otherwise
    signal lts[outLen] <== LTBitVector(outLen)(length);
    for (var i = 0; i < outLen; i++) {
        out[i] <== in[i] * lts[i];
    }
}

/**
SliceGrouped: Same functionality as Slice but more efficient!
Works by grouping the inputs and then slicing the grouped array.

Cost: (g = numsPerGroup)
    - Slice: (inLen / g) + (outLen / g) + ((outLen * inLen) / (2 * g))
    - Multiplexer: outLen * g
    - SliceFromStart: outLen * 2
Note: Doesn't include ConvertBase costs. Segments2NumBE and DivideMod2Power are negligible.

Range checks:
    - index in [0, inLen)
    - length in (0, outLen]
    - index + length in [0, inLen]
    - numsPerGroup is a power of 2 (checked at compile time)

SliceGrouped(inWidth, inLen, outLen)(in, index, length)：效果和返回的结果与Slice(inLen, outLen)(in, index, length)。
这里多了一个inWidth来表示in里元素的比特位宽度，一般来说都是8位（一个字节）。以能用group方式，来提高分片的效率。
**/
template SliceGrouped(inWidth, inLen, outLen) {
    var numsPerGroup = 16; // since inWidth is 8 (in SliceEfficient), this is the maximum we can set
    signal input in[inLen];
    signal input index;
    signal input length;

    RangeCheck(numBits(inLen), inLen - 1)(index); // index in [0, inLen - 1]
    RangeCheck(numBits(outLen), outLen - 1)(length - 1); // length in [1, outLen]
    RangeCheck(numBits(inLen), inLen)(index + length); // index + length in [0, inLen]

    var groupedInWidth = numsPerGroup * inWidth;  // inWidth是in中元素的位长，即其代表的比特位数。
    assert(groupedInWidth < 253);  // 2^253是标量域的大小

    var groupedInLen = ceil(inLen, numsPerGroup);  // in的分组个数

    // 对in分组
    //   - numsPerGroup：每组元素个数，为16。
    //   - groupedInLen：组的个数，为inLen除以numsPerGroup，向上取整
    //
    // 对每组做inWidth进制转换，放进数组inGrouped中。inGrouped的每个元素就代表原始数组in的一个组。
    //   - groupedInWidth：每个组的比特位长度，为numsPerGroup*inWidth（组元素个数*每个元素的比特位长度）。
    signal inGrouped[groupedInLen];
    for (var i = 0; i < groupedInLen; i++) {
        var arr[numsPerGroup];
        for (var j = 0; j < numsPerGroup; j++) {
            if (i * numsPerGroup + j < inLen) {
                arr[j] = in[i * numsPerGroup + j];
            } else {
                arr[j] = 0;
            }
        }
        inGrouped[i] <== Segments2NumBE(numsPerGroup, inWidth)(arr);
    }

    signal startIdxByP, startIdxModP, endIdxByP, _endIdxModP; // P = numsPerGroup

    var L = logBase2(numsPerGroup); // 2^l = numsPerGroup
    assert(L != -1); // This requirement comes from DivideMod2Power
    var maxNumBits = numBits(inLen);
    // DivideMod2Power(n, p)(in) = (in / 2^p, in % 2^p)
    // 在下面，2^L就是每组的元素个数
    // 在分组后，index（切分in的起点）所表示的元素在第startIdxByP组的第startIdxModP个元素里。
    (startIdxByP, startIdxModP) <== DivideMod2Power(maxNumBits, L)(index);
    // 同理，index + length - 1（切分in的末尾）所表示的元素在第endIdxByP组的第_endIdxModP个元素里。
    (endIdxByP, _endIdxModP) <== DivideMod2Power(maxNumBits, L)(index + length - 1);

    /**
        Q) Given a list of elements chunked into groups of size g and length of the sublist n,
            return the maximum number of groups that the sublist can span.
            计算长度为n的sublist最多要跨过几个group，每个group的长度为g。
            这里就是计算，输出长度outLen有几个group，每个group的长度为numsPerGroup。
        A) First note that the number of groups is maximum when the sublist starts at the end of a group (i.e.,
            the first element of the sublist is the last element of the group).

            - If the sublist starts at the beginning of a group, then the number of groups is ceil(n / g).
            - So in the worst case, i.e., when the sublist starts at the end of a group, the number of groups is
                ceil((n-1) / g) + 1.
    **/
    var groupedOutLen = 1 + ceil(outLen - 1, numsPerGroup); // See explanation above
    // 切分inGrouped后得到新数组outGrouped。
    // 我们要得到in[index:index+length-1]。但由于inGrouped已经做了分组，所以前面做了下标的转换。
    signal outGrouped[groupedOutLen] <== Slice(groupedInLen, groupedOutLen)(
        inGrouped, startIdxByP, endIdxByP - startIdxByP + 1
    );

    var X = numsPerGroup * groupedOutLen;
    // 前面的inGrouped和outGrouped的元素位长是groupedInWidth（numsPerGroup * inWidth）。
    // 现在重新转换回元素位长为inWidth的数组，其长度为X。
    signal outFinal[X] <== ConvertBase(groupedInWidth, groupedOutLen, inWidth, X)(outGrouped);

    // Assertion only for illustrative purposes. It is always true if groupedOutLen is set as above.
    assert((outLen - 1) + (numsPerGroup - 1) <= X - 1);

    signal outOptions[outLen][numsPerGroup];
    for (var i = 0; i < outLen; i++) {
        for (var j = 0; j < numsPerGroup; j++) {
            //      index      0   1   2   3   4   5   6   7   8   9 ...   16
            //    outFinal     a0  a1  a2  a3  a4  a5  a6  a7  a8  a9 ...  a16
            // outOptions[0]   a0  a1  a2  a3  a4  a5  a6  a7  a8  a9 ...  a16
            // outOptions[1]   a1  a2  a3  a4  a5  a6  a7  a8  a9  a10 ... a17
            // outOptions[2]   a2  a3  a4  a5  a6  a7  a8  a9  a10 a11 ... a18
            outOptions[i][j] <== outFinal[i + j];
        }
    }
    // Note: We are able to do the below two steps only because numsPerGroup is 2^4 = 16.
    signal selector[4] <== Num2Bits(4)(startIdxModP);  // 将startIdxModP变成4位的二进制数组
    // MultiMux4(n)(c, s)：对c的每一行都选择出下标为s的元素。c是c[n][16]，s是s[4]，s[4]是二进制表示。
    //   - Mux是multiplexer的缩写，是电路里常用的多路选择方法。
    //   - MultiMux4源码：https://github.com/iden3/circomlib/blob/master/circuits/mux4.circom#L21
    // 切片的start是第startIdxByP组的第startIdxModP个元素。这里整体往右做了startIdxModP个元素的偏移。
    signal outWithSuffix[outLen] <== MultiMux4(outLen)(outOptions, selector);
    signal output out[outLen] <== SliceFromStart(outLen, outLen)(outWithSuffix, length);
}

/**
SliceEfficient: A wrapper around SliceGrouped.

Has the same function signature as Slice and can be used as a drop-in replacement.

SliceEfficient(inLen, outLen)(in, index, length) = SliceGrouped(8, inLen, outLen)(in, index, length)
**/
template SliceEfficient(inLen, outLen) {
    var inWidth = 8;
    signal input in[inLen];
    signal input index;
    signal input length;

    signal output out[outLen] <== SliceGrouped(inWidth, inLen, outLen)(
        in, index, length
    );
}

/**
Checks if an ASCII-encoded substring exists in a Base64-encoded string.

Construction Parameters:
    b64StrLen:              The length of the Base64-encoded string
    maxA:                   The maximum length of the ASCII-encoded substring

Input:
    b64Str[b64StrLen]:      The Base64-encoded string to search in
    lenB:                   The length of the Base64-encoded substring to check
    BIndex:                 The index of the first character of the
                            Base64-encoded substring to check. For the check to
                            work, it should represent just the part of b64Str that
                            contains A.
    A[maxA]:                The ASCII-encoded substring to search for padded with 0s
                            e.g., A = "sub":"12345",0000 and lenA = 14
    lenA:                   The length of the ASCII-encoded substring
    payloadIndex:           The index of the first character of the payload

Output:
    The function checks if the ASCII-encoded substring exists in the
    Base64-encoded string with an offset of 0, 1, or 2.

Range checks:
    0 < lenB <= maxB (checked in Slice)
    0 <= BIndex < b64StrLen (checked in Slice)
    0 <= BIndex + lenB <= b64StrLen (checked in Slice)
    maxB <= b64StrLen (checked in Slice)
    0 < lenA <= maxA (checked in LTBitVector)
    payloadIndex <= BIndex (checked in RemainderMod4)

Cost: (128 + (b64StrLen / 32)) * maxA
Breakdown:
    - 96 * maxA (MultiBase64URLToBits) where (96 ~ 73 * (4/3))
    - (b64StrLen * maxA) / 32 (SliceEfficient)
    - 8 * maxA (Num2BitsBE)
    - 24 * maxA (AssertEqualIfEnabled)

ASCIISubstrExistsInB64(b64StrLen, maxA)(b64Str, lenB, BIndex, A, lenA, payloadIndex)
*/
template ASCIISubstrExistsInB64(b64StrLen, maxA) {
    // Note: Ideally, we should implement the b64Len function from jwtutils.ts in circom and call b64Len(maxA, i) for any i.
    //  For simplicity, we avoid it and instead pick the maximum value this function can return.
    var maxB = 4 * (1 + floor(maxA, 3));

    signal input b64Str[b64StrLen];
    signal input lenB;
    signal input BIndex;
    signal B[maxB] <== SliceEfficient(b64StrLen, maxB)(
        b64Str, BIndex, lenB
    );

    var B_bit_len = maxB * 6;
    signal B_in_bits[B_bit_len] <== DecodeB64String(maxB)(B, lenB);

    signal input A[maxA];
    signal input lenA;

    var A_bit_len = 8 * maxA;
    signal A_in_bits[A_bit_len];
    for (var i = 0; i < maxA; i++) {
        var X[8] = Num2BitsBE(8)(A[i]);
        for (var j = 0; j < 8; j++) {
            A_in_bits[i * 8 + j] <== X[j];
        }
    }

    signal input payloadIndex;
    var BIndexInPayload = BIndex - payloadIndex;
    signal expectedOffset <== RemainderMod4(numBits(b64StrLen))(BIndexInPayload);
    signal eq_0 <== IsEqual()([expectedOffset, 0]);
    signal eq_1 <== IsEqual()([expectedOffset, 1]);
    signal eq_2 <== IsEqual()([expectedOffset, 2]);
    eq_0 + eq_1 + eq_2 === 1; // ensure offset is 0, 1, or 2

    signal tmp[maxA] <== LTBitVector(maxA)(lenA);

    signal enabled_0[maxA];
    // A_bit_len <= B_bit_len is guaranteed by the condition on maxB
    assert(A_bit_len <= B_bit_len);
    for (var i = 0; i < A_bit_len; i++) {
        if (i % 8 == 0) {
            enabled_0[i \ 8] <== tmp[i \ 8] * eq_0;
        }
        AssertEqualIfEnabled()(enabled_0[i \ 8], [A_in_bits[i], B_in_bits[i]]);
    }

    signal enabled_1[maxA];
    // A_bit_len + 2 <= B_bit_len is guaranteed by the condition on maxB
    assert(A_bit_len + 2 <= B_bit_len);
    for (var i = 0; i < A_bit_len; i++) {
        if (i % 8 == 0) {
            enabled_1[i \ 8] <== tmp[i \ 8] * eq_1;
        }
        AssertEqualIfEnabled()(enabled_1[i \ 8], [A_in_bits[i], B_in_bits[i + 2]]);
    }

    signal enabled_2[maxA];
    // A_bit_len + 4 <= B_bit_len is guaranteed by the condition on maxB
    assert(A_bit_len + 4 <= B_bit_len);
    for (var i = 0; i < A_bit_len; i++) {
        if (i % 8 == 0) {
            enabled_2[i \ 8] <== tmp[i \ 8] * eq_2;
        }
        AssertEqualIfEnabled()(enabled_2[i \ 8], [A_in_bits[i], B_in_bits[i + 4]]);
    }
}
