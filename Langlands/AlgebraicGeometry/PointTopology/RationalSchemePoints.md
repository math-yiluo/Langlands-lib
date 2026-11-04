# Identity-test points with the scheme-chart topology

Worker 1045 wrote this module and this explanation. It is an internal
transport layer. The published scheme-point topology lives on base-valued
points `RingPoint R X R`. Group schemes use identity-test points
`RationalPoint R X`. This module moves the published chart-topology results
to identity-test points without assuming the scheme is affine.

## Definitions

Let `R` be a commutative ring with a topology and let
`X : Over (Spec R)`.

- `rationalSchemeTopology R X` is the topology on `RationalPoint R X`
  induced along the published bijection `rationalPointEquiv R X` from
  `schemePointTopology R X R`. That is the final topology from all affine
  open charts, defined in `PointTopology.SchemePoints`.
- `rationalSchemePointHomeomorph R X` is `rationalPointEquiv R X`, viewed as
  a homeomorphism between these two chart topologies.
  `rationalSchemePointHomeomorph_apply` records that it is this bijection.

## Results

- `rationalPointTopology_eq_rationalSchemeTopology`: if `X.left` is affine,
  the published identity-test evaluation topology `rationalPointTopology R X`
  equals `rationalSchemeTopology R X`. Both are induced along
  `rationalPointEquiv R X`, and the published
  `schemePointTopology_eq_affine` identifies the chart topology with the
  affine evaluation topology on base-valued points.
- `rationalPointMap_eq_comp`: postcomposing an identity-test point with a
  morphism `f : X ⟶ Y` agrees with postcomposing the corresponding
  base-valued point with `f`, conjugated by the two bijections. This follows
  from `rationalPointEquiv_natural`. It needs no topology.

Each of the remaining results also assumes that `R` is a topological ring,
a local ring, and has open units (`IsOpenUnits R`). All of them use
`rationalSchemeTopology` on every scheme involved.

- `continuous_rationalSchemePointMap`: postcomposition with any `f : X ⟶ Y`
  is continuous. Source: `schemePointContinuity_proof`.
- `isOpenEmbedding_rationalSchemePointMap`: if `f.left` is an open
  immersion, postcomposition is an open embedding. Source:
  `isOpenEmbedding_schemePointMap`.
- `isEmbedding_rationalSchemePointMap`: if `f.left` is a closed immersion,
  postcomposition is an embedding. Source:
  `isEmbedding_schemeClosedPointMap`.
- `continuous_rationalSchemePointPair`: the pairing
  `(p, q) ↦ lift p q` from `RationalPoint R X × RationalPoint R Y` to
  `RationalPoint R (X ⊗ Y)` is continuous. Source:
  `continuous_schemePointPair`. The product equation compares projections
  with `CartesianMonoidalCategory.hom_ext`, using `rationalPointEquiv_natural`
  and `lift_fst`/`lift_snd`.

In each case the proof writes the identity-test map as the base-valued map
conjugated by `rationalSchemePointHomeomorph`, and composes with the cited
published result. The cited results are in `PointTopology.SchemeOpenPointProofs`,
`PointTopology.SchemeTopologyExistenceProofs`,
`PointTopology.SchemeClosedPointProofs` and `PointTopology.SchemeProducts`.

## Provenance

This module only translates between two point conventions. It adds no
external mathematical content beyond the cited published Library results.
