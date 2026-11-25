# Base change of the lifting data

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. For a `C`-algebra
`C'`, the base-changed data are:
- `bcI C' = I C'` (`redIdeal`);
- `bcx₀ x₀ C' = Spec.map (redStruct I C') ≫ x₀`;
- `bcs s C' = Spec.map (strMap C') ≫ s`.

The following hold.
- `isLift_iff_isGlobalLift` (`Iff.rfl`): lifts on `C'` of the original
  data are exactly global lifts of the base-changed data.
  `IsGlobalLift.res` and `GLift.res` restrict global lifts along
  `C → C'`.
- `Chart.bc` transports a chart along `C → C'`, with the same affine opens
  and the image of the chart element.
- `Chart.rep_bc` says that chart representatives do not change, proved by
  the uniqueness of chart representatives (`chartRep_eq`).
- `restrC_restrC` composes restrictions along a scalar tower.
  `affComb_congr_ideal` says that `affComb` does not depend on the ideal
  used to justify it.
- `gcomb_res`: restriction from `C` to `C'` commutes with global affine
  combinations, with coefficients mapped by `algebraMap C C'`. The proof
  compares chart representatives on a covering family of transported
  charts.

These are internal lemmas for the lifting of homomorphisms from groups of
multiplicative type through nilpotent thickenings. They are used for
the naturality of square-zero kernels of group schemes along maps of test
algebras.
