# Proof of the actual fixed-model adelic point comparisons

The theorem `adelicFixedModelPointComparison` proves exactly
`AdelicFixedModelPointComparisonStatement` in an arbitrary common universe.
The two component theorems give the curve-place and full number-field
properties separately. The scope and source context are recorded in the
unchanged target's Markdown.

For each actual fixed initial integer base, apply the published theorem
`filteredRingPointComparison` to the actual algebra diagram, its actual
full-adele cocone, and the proved `curvePlaceAdeleOverIsColimit` or
`numberFieldAdeleOverIsColimit`. The generic theorem concerns actual relative
scheme morphisms and allows arbitrary nonaffine models. It supplies
injectivity and both eventual-equality criteria under locally finite type.
Translate the morphisms of the finite-superlevel indexing poset to their
inclusion inequalities by `leOfHom`, and translate back by `homOfLE`.
The diagram's maps are definitionally the actual coefficient inclusions,
so these are precisely the stated same-stage and two-stage criteria.

Under locally finite presentation, the same generic theorem gives stage
factorization and bijectivity of the canonical comparison. Apply
`ringPointColimitHomeomorph` with that bijectivity and the original
`curvePlaceFixedModelStageTopology` or
`numberFieldFixedModelStageTopology`. Its underlying function is the very
comparison used in the target, and its domain and codomain topologies are
the two specified final topologies. Its `isHomeomorph` theorem gives the
last assertion. This step requires no independent theorem about openness
of arithmetic transitions, because both topologies here are final from
the same transported original stages. It makes no additional claim about
generic fibers, model independence or the further adelic topology.
