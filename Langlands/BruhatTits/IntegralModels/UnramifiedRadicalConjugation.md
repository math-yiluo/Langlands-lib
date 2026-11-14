# Conjugating special-fibre preimages into an unramified apartment

This internal derived module supplies the conjugation step in reducing the
descended radical-generation problem to a computation in an apartment over
the maximal unramified extension. It uses existing Library transport and
normality results and makes no new assertion from the literature.

For an isomorphism `f : G ≅ H`, the existing `IntegralModel.transport`
keeps the integral group scheme, sections, special fibre, and reduction
map. It changes generic evaluation by `rationalPoints.map f.hom`.
`transport_specialFibreSubgroupPoints` therefore carries the generic
preimage of every subgroup `P` of the special-fibre point group to its
image under that rational-point map. The proof carries the same integral
section through both directions of subgroup-image membership.

`specialFibreSubgroupPoints_eq_map_innerIso` recovers the original
preimage from its computation on the model transported by `Int(g⁻¹)`.
It uses the preceding theorem, the published
`rationalPoints_map_innerIso`, and cancellation of the two conjugations.
The subgroup `P` is unchanged because transport changes only the generic
identification.

`integralPoints_transport_innerIso_same_zeroDatum` works for any affine
group carrying the supplied maximal-unramified building data over the
actual inertia-fixed field. If a model has integral points
`E.zeroPoints ⊓ Fix(g · Y)`, its transport by `Int(g⁻¹)` has integral
points `E.zeroPoints ⊓ Fix(Y)`. The proof uses the unconditional
`UnramifiedZeroDatum.normal_zeroPoints` from
`UnramifiedSplitBoundedPoints` to preserve the same zero subgroup. The
pointwise fixer transforms by the published action lemma
`SubMulAction.fixingSubgroup_map_conj_eq`. Injectivity of the rational-point
isomorphism allows its subgroup-image map to commute with the intersection.
No independence theorem for different zero data is assumed.

All constructions retain arbitrary universe `u`. These lemmas require
neither smoothness nor any nonemptiness or facet condition on `Y`.
They do not identify a quotient kernel with an actual radical and do not
prove the root-generation formula. Those are separate inputs to the
application.
