# Regular sections with the same zero ideal differ by a unit

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal`.

- `IsRegularSection L σ`: multiplication by `σ` is injective over every open (`c • σ|_W = 0`
  implies `c = 0`).
- `isRegularSection_of_local`: regularity follows from regularity of the local coordinates on an
  affine cover by frames.
- `exists_isUnit_eq_smul_of_zeroIdeal_eq`: if `σ` is regular and `σ'` has the same zero ideal,
  then `σ' = c • σ` for a unit `c ∈ Γ(X, ⊤)`. On each frame the coordinates generate the same
  principal ideal, so they differ by a local unit; the local units agree on overlaps by
  regularity and glue by the sheaf property.

## Source

Kleiman, *The Picard scheme*, p.25, proof of Theorem 3.13: a relative effective divisor determines
its section up to a unit (with `Γ(O) = Γ(O_T)` by Exercise 3.11, used in `LinearSystemAffineInjective`).
