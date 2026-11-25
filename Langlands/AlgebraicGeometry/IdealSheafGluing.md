# Gluing ideal sheaves from affine opens

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.IdealSheafGluing`.

- `extend U J`, `extend_ideal`, `exists_ideal_eq`: an ideal of `Γ(X, U)` on an affine open `U`
  extends to an ideal sheaf of `X` (Mathlib's `IdealSheafData.map` along `U.ι`), and finitely
  many compatible ideals on affine opens with affine inclusions glue to one ideal sheaf (the
  infimum of the extensions).
- `eq_of_comap_eq`: two ideal sheaves whose pullbacks to the members of an open cover agree are
  equal.
- `eq_of_comap_eq'`: the same along a jointly surjective family of open immersions.

The last two are used throughout the proof to compare ideal sheaves locally
(Mathlib's `IdealSheafData.ext_of_iSup_eq_top` and `ideal_comap_of_isOpenImmersion`).
