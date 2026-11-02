# Descent categories under pullback-preserving reindexing

For categories `C` and `D`, a functor `G : C ⥤ D`, and a pseudofunctor
`F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat`, this module constructs an equivalence

`(G.op.toPseudofunctor.comp F).DescentData f ≌ F.DescentData (fun i ↦ G.map (f i))`.

Here `f i : X i ⟶ S` is an arbitrary indexed family. The construction takes
chosen pairwise pullbacks `sq i j` of the family, chosen threefold pullbacks
`sq₃ i j k`, and the assumption that `G` preserves pullbacks. No topology or
stack assumption is used. The category of values of `F` is not required to be
a groupoid. The universes of the index type, both base categories, and the
categories of values are independent.

The exported construction is
`Langlands.CategoryTheory.StackPullback.descentDataEquivalence`.
`reindex` abbreviates the composite pseudofunctor.

The proof first establishes that the flexible composition isomorphism
`mapComp'` for the composite pseudofunctor agrees with the one for `F` on
mapped arrows. This identifies `pullHom`, the conjugated pullback of a
morphism used by Mathlib's descent API. `mapChosenPullback` and
`mapChosenPullback₃` map all structure arrows of the supplied pullbacks
through `G`; their universal properties follow from preservation of pullbacks.
Uniqueness of lifts then identifies the corresponding operation `pullHom'`.

The intermediate equivalence `imageDescentDataPrimeEquivalence` works with
Mathlib's category `DescentData'`. Both functors retain exactly the component
objects and compatibility morphisms. The `pullHom'` comparison transports
the identity and triple cocycle laws in both directions. The unit and counit
are the componentwise identity isomorphisms. Finally, composing this equivalence
with Mathlib's equivalences between `DescentData'` and unrestricted
`DescentData` gives the exported construction. Thus all morphisms, arbitrary
test objects, and coherence conditions of unrestricted descent data are retained.

This is internal categorical infrastructure derived directly from the pinned
Mathlib definitions in `CategoryTheory/Sites/Descent/DescentDataPrime.lean`
and `CategoryTheory/Bicategory/Functor/LocallyDiscrete.lean`. It is not a
translation of a separate literature assertion. In the line-bundle fpqc stack
task it supplies the descent-category comparison needed for relative transport;
this module alone does not assert the stack property for any topology.
