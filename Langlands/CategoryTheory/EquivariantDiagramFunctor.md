# Functors on varying-group equivariant diagrams

Author: Worker 13.

This is an internal categorical construction extending
[EquivariantDiagram](EquivariantDiagram.md). Fix a category `I`, an actual
group functor `D : I ⥤ GrpCat`, and categories `C` and `E`. The group universe,
the index-object and index-morphism universes, and the object and morphism
universes of both categories are independent.

For an actual functor `F : C ⥤ E`, `mapFunctor F` is a functor

`EquivariantDiagram D C ⥤ EquivariantDiagram D E`.

For a diagram `M`, its underlying diagram is `M.obj ⋙ F`, its action at `i`
sends `g` to `F.map (M.ρ i g)`, and its transition at an arrow `f` is
`F.map (M.obj.map f)`. The action is the composite of the original action
homomorphism with Mathlib's `F.mapEnd`. Applying `F` to the original
transition equivariance equation proves the new equivariance equation.
On a diagram morphism `c`, the underlying natural transformation is
`Functor.whiskerRight c.hom F`; its component equivariance follows by applying
`F` to `c.comm`. The identity and composition laws reduce to those of `F`
at every index.

For a natural transformation `α : F ⟶ F'`, `mapNatTrans α` is a natural
transformation between these two functors on equivariant diagrams. At a
diagram `M`, its underlying transformation has component
`α.app (M.obj.obj i)`. Naturality of `α` at the action endomorphism proves
equivariance, and naturality at a component of a diagram morphism proves
naturality in `M`.

`postcompose` packages this construction as the actual functor

`(C ⥤ E) ⥤ (EquivariantDiagram D C ⥤ EquivariantDiagram D E)`.

Its preservation of identity transformations and their composition follows
componentwise from identity and composition of natural transformations.
Thus an actual diagram of functors and natural transformations, such as
power-quotient functors and their transitions, can be transported to varying
group diagrams without adding compatibility hypotheses.

The three final formulas identify the action of `mapFunctor F` at an index
with Mathlib's `F.mapAction`, identify its transition's underlying morphism
with the image of the original transition, and identify the underlying
component of `mapNatTrans α`. These are definitional equalities.

The provenance is functoriality of the published equivariant-diagram
construction and Mathlib's functors, whiskering, `mapEnd`, and `mapAction`.
No additional source definition or theorem from the Harris literature is
claimed. The group diagram is fixed throughout. This file supplies no
coefficient sheaf, geometric cover, torsor comparison, inverse associated
coefficient system, topology, smoothness, or cohomology construction.
