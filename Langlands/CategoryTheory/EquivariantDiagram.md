# Equivariant diagrams over varying groups

Author: Worker 13.

This is an internal categorical construction. Its inputs are an actual
functor `D : I ⥤ GrpCat` and a category `C`. An `EquivariantDiagram D C`
contains an actual functor `F : I ⥤ C`, group actions
`D.obj i →* End (F.obj i)`, and the equation

`ρ_i(g) ≫ F.map f = F.map f ≫ ρ_j(D.map f(g))`.

Thus a transition from index `i` to index `j` intertwines the source action
with the target action restricted along the given group homomorphism.
The groups, index objects, index morphisms, category objects, and category
morphisms have independent universes.

Morphisms are natural transformations of the underlying diagrams that commute
with the action at each index. The category uses identity and composition of
natural transformations; composition is equivariant by the two supplied
equivariance equations and associativity. The category identity and
associativity laws follow from those for natural transformations. The
`forget` functor to ordinary diagrams is faithful.

`action F i` is the Mathlib `Action` at index `i`. `transition F f` is the
actual underlying transition, bundled as a morphism from that source action
to the restricted target action. `evaluation i` sends morphisms to their
equivariant component at `i`. `reindex E F` precomposes the underlying
diagram and the group diagram by the same functor `E`; its equivariance is
the original equation at `E.map f`.

The construction reuses Mathlib functors, natural transformations, `GrpCat`,
`Action`, and `Action.res`. It packages their compatibility without requiring
equal groups at different indices. In particular, an inverse diagram of
deck-group quotients can act on a diagram of covers or coefficient modules.
No coefficient sheaf, comparison isomorphism, geometric torsor, or scheme
existence result is supplied or constructed here.
