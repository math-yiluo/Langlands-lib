# Rational rows and the parabolic `P'_n(F)`

Module `Langlands.Global.RankinSelberg.EqualAnalyticRationalRows`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`. Here `n = r + 1`, and `rowOf F r γ` is the
last row `e_n γ` of `γ ∈ GL_n(F)`, as a `1 × n` rational matrix.

## The parabolic

- `rowOf_mul`, `rowOf_one_mul`, `rowOf_ne_zero` (an invertible matrix has nonzero last row).
- `lastRowScalarSubgroup`: the matrices whose last row is a multiple of `e_n`.
- **`eisensteinParabolic_eq`**: the Library's `eisensteinParabolic F r`
  (`mirabolic ⊔ center`, `P'_n = Z_n P_n`) equals `lastRowScalarSubgroup`. One inclusion holds
  because mirabolic and scalar matrices have last rows `e_n` and `u e_n`. Conversely, a matrix
  with last row `a e_n` is `(a I)(a⁻¹ p)` with `a⁻¹ p` mirabolic; Mathlib's
  `center_eq_range_scalar` describes the centre. Consequences: `mem_eisensteinParabolic_iff`
  and `mk_eq_mk_iff_rowOf` (`P'γ = P'γ'` iff `e_n γ'` is a multiple of `e_n γ`).
- `exists_rowOf_eq`: every nonzero row is the last row of an invertible matrix (permuted
  update of the identity; the same construction as the Library's
  `exists_lastRow_eq_of_ne_zero`).
- **`cosetRowEquiv`**: `(q, t) ↦ t · e_n q.out` is a bijection
  `P'_n(F) \ GL_n(F) × F^× ≃ F^n ∖ 0` (`cosetRowMap_bijective`).

## Ideles and last rows

- `ratUnit F f` is the principal idele `f ∈ F^×` as a point of `GL_1(𝔸)`. `ratUnitEquiv` is the
  bijection `F^× ≃ GL_1(F)`, and `ideleOf (ratUnit f)` is the diagonal unit of `f`
  (`ideleOf_ratUnit`).
- `lastRow_eq`, `lastRow_rationalPoint_mul`: the Library `lastRow F r (γ g)` is
  `e_n γ · g`.
- **`ideleOf_smul_lastRow`**: `det(ratUnit f · z) · e_n γ g = (f e_n γ) · (z g)`, where `z g`
  means `ζ(z) g`. This turns the terms of the Eisenstein series into theta terms.

## Provenance

The bijection `P'(F) \ GL_n(F) ≃ (F^n ∖ 0)/F^×` underlies the unfolding in Cogdell 2004,
§2.3, printed p.208 (the Eisenstein series as a sum over `P'(k) \ GL_n(k)` becomes the theta
series). The proofs are internal.
