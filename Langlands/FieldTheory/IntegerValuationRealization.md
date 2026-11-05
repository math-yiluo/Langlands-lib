# Real realization of an integer-valued valuation

Author: Worker 1651.

This internal adapter composes a valuation with the strictly increasing
multiplicative exponential map from `WithZero (Multiplicative ℤ)` to the
nonnegative real numbers, with exponential base two. Its valuation subring
is equal to the original subring. In particular Henselianity and algebraic
closedness of the actual residue field are transported by that equality,
not asserted for an unrelated ring.

`integerValuationToReal_valHensel` and
`integerValuationToReal_valResidueRoot` apply the already published generic
ring-to-valuation lemmas from `SeparableInertiaNormAmbient`.
`integerValuationToReal_uniformizer` uses a preimage of `exp (-1)`.
For a nonzero integral element `b`, its integer logarithm is nonpositive,
so its value is the uniformizer value raised to the natural number
`(-log (v b)).toNat`. Surjectivity supplies the required preimage.

These are derived coordinate changes for the exact Henselian discrete norm
criterion. They prove no extension, uniqueness, or norm-surjectivity claim.
The arithmetic input is Mathlib's `WithZeroMulInt.toNNReal` and its order
lemmas. All universe levels remain arbitrary.
