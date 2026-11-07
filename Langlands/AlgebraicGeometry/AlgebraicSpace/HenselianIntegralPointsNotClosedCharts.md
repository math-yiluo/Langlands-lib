# Charts and affine-line points for the counterexamples to Corollary 5.7 closedness

Author: Worker 105.

Helper module for the proofs of the counterexamples to the closedness assertion of
Corollary 5.7 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.16
(`HenselianIntegralPointsNotClosedOfFiniteTypeStatement` and
`HenselianIntegralPointsNotClosedOfSeparatedStatement`). It contains no statement from the
literature.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosed`.

For a commutative ring `R`:

- Instances: `ringTest R R[X]` (the affine line `Spec R[X]` over `Spec R`) is locally of
  finite type (`HasRingHomProperty.Spec_iff`, `R[X]` is finitely generated) and
  quasi-compact over `Spec R`.
- `linePoint R s : RingPoint R (ringTest R R[X]) T`: for an `R`-algebra `T` and `s ∈ T`, the
  point `ringTestMap R (aeval s)` with coordinate `s`. Giving it the type `RingPoint` (rather
  than a bare morphism of `Over (Spec R)`) lets rewriting see through the point equivalences.
- `affineRingPointEquiv_ringTestMap`: `affineRingPointEquiv R R[X] T (ringTestMap R φ) = φ`
  (`Spec.preimage_map`).
- `eq_linePoint`: every point `a` of the affine line is `linePoint R` of its coordinate, the
  value at `X` of `affineRingPointEquiv R R[X] T a`.

For a commutative ring `O` and a nontrivially normed field `K` that is an `O`-algebra:

- `baseChangeChart K U f hf`: for `U` locally of finite type and quasi-compact over
  `Spec O` and a morphism `f : h_U → X` of algebraic spaces over `Spec O` with `hom f`
  étale, the base change to `Spec K` as an `EtaleFiniteTypeChart K X_K`, where
  `X_K = baseChange (Spec.algebraMap O K) X`. The chart scheme is `ringBaseChange O K U`
  and the chart map is `homMk (restrictAtlas (Spec.algebraMap O K) (hom f))`. It is étale by
  `relative_restrictAtlas`; finite type is stable under base change. This copies the
  Library's `EtaleFiniteTypeChart.completion` with the base `O` in place of a field.
- `baseChangeRingPointsEquiv_baseChangeChart_pointMap`: the chart map of
  `baseChangeChart K U f hf`, read on `K`-points of `X` through `baseChangeRingPointsEquiv`,
  is `RingPoints.map f` after `(ringPointBaseChangeEquiv O K K U).symm`. This is the
  Library's `HenselianIntegralPointsOpen.baseChangeRingPointsEquiv_schemePointsMap`.
- `continuous_linePoint`: `s ↦ linePoint O s` is continuous from `K` to
  `schemePointTopology O (ringTest O O[X]) K`. That topology is the affine one
  (`schemePointTopology_eq_affine`), which `spectrumAlgebraPointHomeomorph` identifies with
  the evaluation topology on `O[X] →ₐ[O] K` (`AlgPoint.continuous_iff`). The value of the
  point `s` at `q ∈ O[X]` is `aeval s q`, continuous in `s` (`Polynomial.continuous_aeval`).
