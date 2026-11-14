# Relative effective Cartier divisors are local on an open cover

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveLocal`.

- `ideal_image_eq_span`: a principal ideal of a pulled-back ideal sheaf on an affine open of an
  open subscheme is the transport of a principal ideal of the original ideal sheaf.
- `isRelativeEffectiveCartierIdeal_of_cover`: let `h i : Z i ⟶ X` be jointly surjective open
  immersions over flat maps `j i : S' i ⟶ S` of bases. If each pullback `I.comap (h i)` is relative
  effective Cartier over `S' i` and has local regular generators, then `I` is relative effective
  Cartier over `S`. Cartier-ness follows from `LocalEquationCartier.isEffectiveCartierIdeal_of_local`,
  flatness from Mathlib's locality of flatness on the source (`IsZariskiLocalAtSource.of_openCover`).
