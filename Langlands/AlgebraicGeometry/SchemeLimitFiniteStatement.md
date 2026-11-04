# Finite-morphism detection in actual affine scheme diagrams

This internal prerequisite supports the finite-morphism clause of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source concerns finitely presented models, including nonaffine ones.
This statement isolates an affine-diagram step needing only local finite
type at one stage; it is derived internal content.

`AffineDiagramFiniteDescent` quantifies two actual diagrams of affine
Mathlib schemes over a small cofiltered category, a natural transformation,
actual limit cones with their universal-property witnesses, and a compatible
morphism between the limit schemes. All object, morphism and ring-carrier
sizes share arbitrary universe u.

Choose a stage i₀ at which the component morphism is locally of finite
type. For every actual arrow r : j ⟶ i₀, require that the square with top
map E.map r, left map α.app j, right map α.app i₀ and bottom map F.map r
is a pullback. If the compatible limit morphism is finite, there is a stage
j, an actual arrow j ⟶ i₀ and a finite morphism α.app j. Finiteness here is
the usual scheme property: an affine morphism whose maps on sections over
affine opens make their target rings finite modules over their source rings.
Transition maps need not be injective on coordinate rings. There is no
noetherian or finite-presentation assumption in this intermediate assertion.

The provenance is the affine coordinate-ring argument. Apply actual global
sections to opposite diagrams and cones. Preservation of affine limits gives
ring colimit witnesses, and the cone equations give the actual compatible
global-sections map. Cartesian squares of affine schemes give ring pushouts.
Local finite type gives finite type of the initial ring map, while the finite
limit morphism gives a finite ring map. The filtered-ring finiteness assertion
then produces a later finite ring map, which gives a finite morphism between
the affine schemes at that stage.

The paired Lean file defines the proposition only. Its proof, the reduction
from nonaffine models, target-cover gathering, the reverse implication by
base change, the original filtered-ring specialization and the other clauses
of Theorem 3.4 remain separate obligations.
