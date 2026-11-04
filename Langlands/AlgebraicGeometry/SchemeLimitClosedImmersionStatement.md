# Closed-immersion detection in actual affine scheme diagrams

This derived prerequisite supports the closed-immersion clause of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad's theorem concerns finitely presented models, including nonaffine
ones. This statement isolates a more general affine-diagram step with
local finite type at one stage; it does not assert the full model theorem.

`AffineDiagramClosedImmersionDescent` quantifies two actual diagrams of
affine Mathlib schemes over a small cofiltered category, a natural
transformation, actual limit cones with their universal-property
witnesses, and a compatible morphism between their limit schemes.
All object, morphism and ring-carrier sizes use the arbitrary universe `u`.

Choose a stage `i₀` at which the component morphism is locally of finite
type. For every actual arrow `r : j ⟶ i₀`, require the square whose top
map is `E.map r`, left map is `α.app j`, right map is `α.app i₀`,
and bottom map is `F.map r` to be a pullback. If the compatible limit
morphism is a closed immersion, the conclusion supplies a stage `j`,
an actual arrow `j ⟶ i₀`, and a closed immersion `α.app j`.
Transition maps need not be injective on coordinate rings. No finite
presentation assumption is made for this intermediate assertion.

The provenance is the affine coordinate-ring argument. Apply actual
global sections to the opposite diagrams and cones. Preservation of
affine limits supplies the ring colimit witnesses, and the cone equations
identify the comparison with the actual global-sections map of the limit
morphism. Cartesian squares of affine schemes give ring pushouts.
Local finite type gives finite type of the actual initial ring map, and
a closed immersion gives surjectivity of the limiting ring map. The
filtered-ring finite-type surjectivity assertion then supplies a later
surjective component. Surjectivity of global sections between affine
schemes gives a closed immersion there.

The paired file defines the proposition only. Its proof, the construction
of suitable affine tails from nonaffine models, finite target-cover
gathering, the reverse implication by base change, the original filtered
ring specialization and the other clauses of Theorem 3.4 remain separate
obligations.
