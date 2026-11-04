# Lie dimension and rational point count of split unipotent groups

Worker 1387. This internal module works with the existing finite Ga-series
predicate `RelativeRoot.HasSplitSeries` and the actual dual-number Lie kernel
`lieKernel`. All declarations are in `Langlands.GroupScheme.RelativeRoot`. The
field `k : Type u` is arbitrary except where it is assumed finite.

## Lie dimension of a Ga-series

- `lieDimension_eq_zero_of_range_eq_bot`: if `range (𝟙 H) = ⊥` (every point of
  `H` on every test is the identity), then `Lie.dimension H = 0`. Every element
  of the Lie kernel is a point over `Spec k[ε]`, hence the identity.
- `IsVectorGroupOfDimension.lieDimension`: an actual vector group of dimension
  `d` has `Lie.dimension V = d`. The published `vectorLieCoordinates` gives a
  `k`-linear equivalence of the Lie kernel with `Fin d → k`.
- `IsFppfQuotient.lieDimension_eq_add`: let `j : K ⟶ H` be a closed subgroup
  with `K` smooth, `H` smooth (locally of finite type suffices) and affine, and
  `q : H ⟶ V` an fppf quotient of `H` by `range j` with `V` affine. Then
  `Lie.dimension H = Lie.dimension K + Lie.dimension V`. The proof uses
  rank-nullity for the differential `Lie.targetMapLinear q k`. It is surjective
  because `q` is smooth (`IsFppfQuotient.smooth_of_smooth_kernel` and
  `Lie.targetMapLinear_surjective_of_smooth`). Its kernel is the image of the
  injective differential of `j`: by `IsFppfQuotient.fibers_iff`, a dual-number
  point killed by `q` lies in `range j`, and its lift reduces to the identity
  because `j` is a monomorphism (`mem_lieKernel_of_comp`).
- `HasSplitSeries.lieDimension_eq`: for smooth affine `H`, a Ga-series of
  length `n` gives `Lie.dimension H = n`, by induction on the series using the
  two preceding results.

## Rational points over a finite field

- `IsVectorGroupOfDimension.card_rationalPoints_one`: a one-dimensional vector
  group has `Nat.card k` rational points; its coordinates identify them with
  the global functions of `Spec k`, that is with `k` (`Scheme.ΓSpecIso`).
- `HasSplitSeries.card_rationalPoints`: over a finite field, an affine group
  with a Ga-series of length `n` has `Nat.card k ^ n` rational points (points
  over `Over.mk (𝟙 (Spec k))`). In the inductive step, the map on rational
  points induced by the quotient `q : H ⟶ V` is a group homomorphism. It is
  surjective by the published finite-field torsor theorem
  `finiteFieldTorsorPointStatement`, applied through
  `HomogeneousQuotient.rational_lifts_of_finite_torsor_identity` to the fibres
  of `q`, which are torsors under the smooth connected affine kernel `K`.
  Its kernel is in bijection with the rational points of `K` by the fibre
  criterion. Lagrange's theorem gives the product formula.
- `isIso_of_surjective_rationalPoints`: over a finite field, let `f : V ⟶ U` be
  a closed subgroup with `U` smooth, affine and connected, `V` smooth and
  affine, and both split unipotent (`IsSplitUnipotent`). If every rational
  point of `U` lifts to `V`, then `f` is an isomorphism. The lifting makes the
  rational point sets of `V` and `U` equinumerous, so `q ^ nV = q ^ nU` with
  `q = Nat.card k ≥ 2` and the two series lengths are equal. By the Lie
  dimension result, `Lie.dimension V = Lie.dimension U`, and the published
  `Lie.dimension_lt_of_proper_closedSubgroup` rules out a proper closed
  subgroup.

## Provenance

Internal derivation from the published split-series, fppf-quotient, vector
Lie coordinate, Lie dimension and finite-field torsor results. The point count
`q ^ n` for split unipotent groups over `𝔽_q` is the standard consequence of
Lang's theorem along a composition series with quotients `𝔾_a`. It is used to
show that dynamic contracting subgroups lie in the torus envelope over a
finite field (`FiniteFieldDynamicUnipotentEnvelope`).
