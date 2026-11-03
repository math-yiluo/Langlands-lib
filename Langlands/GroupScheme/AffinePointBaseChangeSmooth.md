# Actual group points under compatible affine base change

Author: Worker 94.

This internal derived construction uses commutative rings `C`, `D` and `A`
in one arbitrary universe, with compatible algebra structures `C → D → A`,
and an actual group scheme `G` over `Spec C`. Its base change `G_D` is the
existing pullback group scheme. The point carriers remain the relative
scheme morphisms from `Spec A`; both group laws are the existing categorical
group-object laws.

`affinePointsBaseChangeMulEquiv` constructs `G(A) ≃* G_D(A)` without an
affineness or topology assumption. It inverts the existing multiplicative
pullback-adjunction comparison `baseChangePointsEquiv`, composed with the
point isomorphism from `ringTestRestrictScalarsIso`. The latter test-scheme
isomorphism has the identity as its underlying spectrum map.
`affinePointsBaseChangeMulEquiv_symm_left` therefore identifies the inverse
map with composition by the first projection of the actual scheme pullback.
Injectivity of that inverse, extensionality of relative morphisms and the
published first-projection formula prove
`affinePointsBaseChangeMulEquiv_eq_ringPoint`: the forward map is exactly
`ringPointBaseChangeEquiv`.

Suppose that the underlying scheme of `G` is affine and `A` has a
topological ring structure. Then
`isHomeomorph_affinePointsBaseChangeMulEquiv` proves that this same map is a
homeomorphism for the original regular-function evaluation topologies. The
proof composes the identity homeomorphism
`affinePointsRingPointHomeomorph` at the source, the published
`isHomeomorph_ringPointBaseChangeEquiv` comparison, and the inverse identity
homeomorphism at the target. The preceding equality identifies the
composite with the multiplicative map.
`affinePointsBaseChangeContinuousMulEquiv` bundles that multiplicative
equivalence with continuity in both directions. Its application lemma is
definitionally the original multiplicative comparison. The local topology
instances in this file are explicit aliases of
`affinePointsTopologicalSpace`, with no change of topology.

For the smoothness comparison only affineness of `G` and an arbitrary
topology on `A` are required. Fix a ring map `c : A → B` into a real normed
commutative algebra `B` in an independent universe. Fix any real model with
corners and any parameter space `M` with its stated topology and charted
space structure. `coordinateSmooth_baseChange_iff` states that a family
`p : M → G(A)` satisfies the existing `G.CoordinateSmooth` predicate if and
only if its image in `G_D(A)` satisfies the corresponding predicate for
`G_D`. Thus every global regular-function value must be infinitely real
differentiable after applying `c`, on each respective group scheme.

The implemented smoothness proof applies
`contMDiff_ringPoint_baseChange_iff` to the underlying affine scheme,
identifies each scheme-point coordinate evaluation with the existing
group-point evaluation by `affineSchemePointEquiv_evaluation`, and uses the
equality of the two actual point maps. The generic theorem already proves
preservation and reflection over all extended coordinates by tensor
induction. `coordinateSmoothBaseChangeFamilyEquiv` restricts precisely the
same point map and inverse to the two subtypes of coordinate-smooth
parameter families, with their inverse laws inherited pointwise.

No continuity of `c`, topological ring hypothesis on `A`, or smooth
manifold hypothesis on `M` is needed for the smoothness comparison. The
construction assigns no manifold structure to either point space and
asserts no Lie group, differential growth, measure or reduction theorem.
Its provenance is the published actual group pullback adjunction, the
actual affine scalar-extension comparison and its regular-function
smoothness theorem, together with the existing identity group/scheme-point
comparisons. It invokes no new external mathematical assertion.
