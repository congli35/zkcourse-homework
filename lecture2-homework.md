# 第2课 课后作业

## 第1题 Num2Bits

template Num2Bits(nBits) {
    signal input in;
    signal output out[nBits];

    for (var i = 0; i<nBits; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
    }
}


## 第2题 IsZero

template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    log("-in: ", -1 * in);
    log("-in: ", -in);

    inv <-- in!=0 ? 1/in : 0;

    out <== 1 - in*inv;
    
    in*out === 0;
}

## 第3题 IsEqual

template IsEqual() {
    signal input in[2];
    signal output out;

    component iszero = IsZero();

    iszero.in <== in[0] - in[1];

    out <== iszero.out;
}

## 第4题 Selector

 template CalculateTotal(n) {
    signal input in[n];
    signal output out;

    signal sums[n];

    sums[0] <== in[0];

    for (var i = 1; i < n; i++) {
        sums[i] <== sums[i-1] + in[i];
    }

    out <== sums[n-1];
}

template Selector(choices) {
    signal input in[choices];
    signal input index;
    signal output out;
   
    component calcTotal = CalculateTotal(choices);
    component eqs[choices];

    // For each item, check whether its index equals the input index.
    for (var i = 0; i < choices; i ++) {
        eqs[i] = IsEqual();
        eqs[i].in[0] <== i;
        eqs[i].in[1] <== index;

        // eqs[i].out is 1 if the index matches. As such, at most one input to
        // calcTotal is not 0.
        calcTotal.in[i] <== eqs[i].out * in[i];
    }

    // Returns 0 + 0 + 0 + item
    out <== calcTotal.out;
}

## 第5题 IsNegative

include "circomlib/compconstant.circom";

template Sign() {
    signal input in[254];
    signal output sign;

    component comp = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);

    var i;

    for (i=0; i<254; i++) {
        comp.in[i] <== in[i];
    }

    sign <== comp.out;
}

template IsNegative() {
    signal input in;
    signal output out;

    component num2Bits = Num2Bits(254);
    num2Bits.in <== in;
    component sign = Sign();
    
    for (var i = 0; i < 254; i++) {
        sign.in[i] <== num2Bits.out[i];
    }

    out <== sign.sign;
}


## 第6题 LessThan

/**

https://stackoverflow.com/questions/73323540/confused-about-circom-lessthan-implementation

Since in[0] < in[1] is not a quadratic expression we have to rewrite the condition a bit to be able to express it as a constraint. The key idea here is to see that in[0] < in[1] is equivalent to in[0] - in[1] < 0. Adding 2^n to both sides we get 2^n + in[0] - in[1] < 2^n.

Now, 2^n = (1 << n) which is where the expression in[0] + (1 << n) - in[1] comes from. The final constraint simply ensures that out = 1 if and only if bit n of 2^n + in[0] - in[1] is 0, which happens exactly when 2^n + in[0] - in[1] < 2^n.
**/

template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
}

## 第7题 IntegerDivide

template RangeProof(bits) {
    signal input in; 
    signal input max_abs_value;

    /* check that both max and abs(in) are expressible in `bits` bits  */
    component n2b1 = Num2Bits(bits+1);
    n2b1.in <== in + (1 << bits);
    component n2b2 = Num2Bits(bits);
    n2b2.in <== max_abs_value;

    /* check that in + max is between 0 and 2*max */
    component lowerBound = LessThan(bits+1);
    component upperBound = LessThan(bits+1);

    lowerBound.in[0] <== max_abs_value + in; 
    lowerBound.in[1] <== 0;
    lowerBound.out === 0;

    upperBound.in[0] <== 2 * max_abs_value;
    upperBound.in[1] <== max_abs_value + in; 
    upperBound.out === 0;
}

// input: n field elements, whose abs are claimed to be less than max_abs_value
// output: none
template MultiRangeProof(n, bits) {
    signal input in[n];
    signal input max_abs_value;
    component rangeProofs[n];

    for (var i = 0; i < n; i++) {
        rangeProofs[i] = RangeProof(bits);
        rangeProofs[i].in <== in[i];
        rangeProofs[i].max_abs_value <== max_abs_value;
    }
}S

template Modulo(divisor_bits, SQRT_P) {
    signal input dividend; // -8
    signal input divisor; // 5
    signal output remainder; // 2
    signal output quotient; // -2

    component is_neg = IsNegative();
    is_neg.in <== dividend;

    signal output is_dividend_negative;
    is_dividend_negative <== is_neg.out;

    signal output dividend_adjustment;
    dividend_adjustment <== 1 + is_dividend_negative * -2; // 1 or -1

    signal output abs_dividend;
    abs_dividend <== dividend * dividend_adjustment; // 8

    signal output raw_remainder;
    raw_remainder <-- abs_dividend % divisor;
    
    signal output neg_remainder;
    neg_remainder <-- divisor - raw_remainder;

    if (is_dividend_negative == 1 && raw_remainder != 0) {
        remainder <-- neg_remainder;
    } else {
        remainder <-- raw_remainder;
    }

    quotient <-- (dividend - remainder) / divisor; // (-8 - 2) / 5 = -2.

    dividend === divisor * quotient + remainder; // -8 = 5 * -2 + 2.

    component rp = MultiRangeProof(3, 128);
    rp.in[0] <== divisor;
    rp.in[1] <== quotient;
    rp.in[2] <== dividend;
    rp.max_abs_value <== SQRT_P;

    // check that 0 <= remainder < divisor
    component remainderUpper = LessThan(divisor_bits);
    remainderUpper.in[0] <== remainder;
    remainderUpper.in[1] <== divisor;
    remainderUpper.out === 1;
}
