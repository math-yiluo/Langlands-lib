# Full restricted-product equivariance of cyclic evaluation

This internal construction extends cyclic evaluation to an intertwiner for the
actual cofinite restricted product. The field, index, local-group and ambient
carrier universes are independent. The cyclic factors remain subspaces of the
ambient carrier. No topology is assumed in this module.

An element trivial at a coordinate commutes with that coordinate's action.
Linear induction extends this identity to its group algebra, and the finite
commuting product extends it to all operators used by stage evaluation.
Consequently, a complementary element fixing the common cyclic generator fixes
every vector in the image of the stage. If the generator is fixed by the full
reference tail outside `E`, the full tail outside every larger stage fixes that
stage's image. This includes infinitely supported reference elements.

`tensorAction` is the published componentwise representation on the actual
restricted tensor direct limit, with the cyclic generator as reference vector at
every coordinate. Its input `he` explicitly requires that the local reference
subgroups fix these generators outside `E`. The separate input `hv` requires
fixedness of the ambient generator under the entire reference tail outside `E`.

On a pure tensor at a stage containing all nonreference coordinates of a group
element, the restricted action is componentwise. Finite-stage equivariance
identifies its evaluation with the finite projection acting on the evaluated
tensor. Full-tail fixedness then identifies this with the whole group element's
action. Such stages are cofinal, so the equality extends to every element of the
direct limit. `evalIntertwiner` bundles this full-group equivariance.

The all-generator tensor evaluates to the ambient generator. When that generator
is nonzero, the intertwiner is nonzero. Ambient irreducibility therefore gives
`eval_surjective`. Assuming also local cyclic irreducibility and scalar
self-intertwiners, the injectivity theorem from `CyclicEvaluationInjective`
combines with surjectivity to construct `evalEquiv`, oriented from the cyclic
restricted tensor representation to the ambient representation.

The provenance is internal: this combines the cyclic evaluation, finite-stage
injectivity, finite/tail decomposition, restricted tensor action and Mathlib's
surjective-or-zero theorem for intertwiners. Local selection, admissibility and
scalar endomorphisms are not derived here. The final Flath existence proposition
also requires packaging the selected factors and its nonzero-reference-vector
convention; it is not asserted by this helper.
