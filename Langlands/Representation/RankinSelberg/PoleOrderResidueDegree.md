# Pole order and residue-degree substitution

This is internal polynomial arithmetic for comparing local Rankin–Selberg
denominators across fields. If `q_E = q_F^f`, the variable `q_E^(−s)` is the
`f`-th power of `q_F^(−s)`. The Library’s
`lPolynomialPoleOrderAtZero` is the multiplicity of the root at `1`. The helper
`lPolynomialPoleOrderAtZero_comp_X_pow` says this multiplicity is unchanged by
substituting `X^f` for `X` in a complex polynomial when `f > 0`. This is the
change of variable for using an identity such as Henniart–Lemaire (2011),
II.4.6(4), printed p. 89, to compare orders at zero. This file does not prove
that identity or any evaluation formula for the certified pair L-factors.

The proof establishes a general domain version under the condition `f ≠ 0`
in the coefficient domain. The zero polynomial is immediate. For a nonzero
polynomial, Mathlib factors it as `(X − 1)^m Q`, where `m` is its multiplicity
and `Q(1) ≠ 0`. Put `H = ∑_{i<f} X^i`. After substitution this equals
`(H^m · Q(X^f)) · (X − 1)^m` by the geometric-sum identity. The first factor
has value `f^m Q(1)` at `1`, which is nonzero. Mathlib's root-multiplicity
formula for multiplication by `(X − 1)^m` gives the same `m`. The complex
case uses characteristic zero to verify the nonzero cast of `f`.
