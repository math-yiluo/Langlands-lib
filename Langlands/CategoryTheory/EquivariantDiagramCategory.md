# Functor-category realization of varying-group equivariant diagrams

This module constructs an equivalence

`Langlands.EquivariantDiagram D C ≌ (Langlands.EquivariantDiagram.Index D ⥤ C)`.

It uses the existing category of diagrams with actions of varying groups, without
changing its objects, morphisms or equivariance equations. The new indexing
category is Mathlib's Grothendieck construction on single-object group categories.
This is an internal categorical derivation from the published
`EquivariantDiagram` and `EquivariantDiagramFunctor` modules and Mathlib's
`CategoryTheory.Grothendieck` and `CategoryTheory.SingleObj` implementations. It
makes no new identification with a construction in the Harris literature.

## Parameters and conventions

The input is a category `I : Type uI` with morphisms in `Type vI`, a covariant
functor `D : I ⥤ GrpCat.{uG}`, and a coefficient category `C : Type uC` with
morphisms in `Type vC`. These five universes are independent. No finiteness,
topology, continuity, commutativity, additivity or limit hypothesis is imposed.
The result describes algebraic group actions in the coefficient category.

For an existing equivariant diagram `M`, its underlying functor is `M.obj`, its
action is `M.ρ i : D.obj i →* End (M.obj.obj i)`, and its transition equation is

`M.ρ i g ≫ M.obj.map f = M.obj.map f ≫ M.ρ j ((D.map f).hom g)`.

Mathlib's `SingleObj G` has one object in universe zero and morphisms in the
universe of `G`. Its categorical composition is `a ≫ b = b * a`. This agrees
with multiplication in `End` and with the monoid-homomorphism convention for
`M.ρ`. In particular, the construction does not reverse the group action.

## Index category and elementary arrows

`groupCategoryDiagram D : I ⥤ Cat.{uG, 0}` sends `i` to `SingleObj (D.obj i)`
and a base arrow to the single-object functor induced by its group homomorphism.
Its identity and composition obligations follow from those of `D`.

`Index D` is the abbreviation `Grothendieck (groupCategoryDiagram D)`. An object
has a base index and the unique fiber object. An arrow from a base `i` to a base
`j` records a base arrow `f : i ⟶ j` and an element of `D.obj j`.
`Index.element` exposes this element with its group type. `Index.id_element`
and `Index.comp_element` prove that identities have element `1` and that

`element (f ≫ g) = element g * (D.map g.base).hom (element f)`.

`Index.hom_ext` proves equality from equality of base arrows and group elements.
This specialized extensionality lemma removes the dependent fiber transports
present in the general Grothendieck extensionality theorem.

`Index.inclusion : I ⥤ Index D` assigns the unique fiber object and gives every
base arrow element `1`. The accompanying base and element lemmas expose its map.
`Index.groupMap i` is a monoid homomorphism from `D.obj i` to endomorphisms of
the included object. It uses Mathlib's Grothendieck fiber inclusion and
`SingleObj.toEnd`; its arrows have identity base and the specified group element.
`Index.comm` proves the required relation between these fiber arrows and base
transitions. All these laws are proved in the actual Grothendieck category.

## Forward and inverse constructions

`toIndexFunctor M` sends an object `x` to `M.obj.obj x.base` and sends an arrow
`f : x ⟶ y` to

`M.obj.map f.base ≫ M.ρ y.base (Index.element f)`.

The composition proof uses the displayed multiplication formula and the original
transition equivariance. `toIndexFunctor_map_inclusion` and
`toIndexFunctor_map_groupMap` recover the original transition and action maps.
`toFunctor` extends this construction to equivariant morphisms, taking the
component at `x` to the original component at `x.base`.

`fromIndexFunctor F` restricts `F` along `Index.inclusion` for its base diagram.
Its action at `i` is the composite of `Index.groupMap i` with `F.mapEnd`.
Functoriality applied to `Index.comm` proves transition equivariance.
`fromFunctor` extends this restriction to natural transformations.

`fromToIso M : M ≅ fromIndexFunctor (toIndexFunctor M)` has identity underlying
components; the two map-recovery lemmas prove its equivariance and naturality.
`toFromIso F : toIndexFunctor (fromIndexFunctor F) ≅ F` uses the equality of each
index object with the inclusion of its base. Its naturality follows by factoring
an arbitrary index arrow as its base inclusion followed by its fiber group
arrow, then applying `F.map_comp`.

`indexEquivalence` supplies the two functors and their natural recovery
isomorphisms to `CategoryTheory.Equivalence.mk`, which produces the coherent
category equivalence. These are implemented functors and isomorphisms, rather
than an assumed equivalence or a record requesting one.

## Scope

The equivalence is reusable infrastructure for homological algebra of
varying-group coefficient diagrams. It does not construct a specific Shimura
level tower, a site, a smooth action, a sheaf comparison, or cohomology. The
companion `EquivariantDiagramAbelian` module uses it to transfer limits, colimits
and abelian structure when the coefficient category has them.
