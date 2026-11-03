# Compactness of points of proper schemes from properness of point maps

This helper module derives the second clause of
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProperties` from
its first clause. Both clauses are stated in
`Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointStatements`.

## `subsingleton_hom_over_id`

For a commutative ring `C` and any `X : Over (Spec C)`, there is at most one
morphism `X ⟶ Over.mk (𝟙 (Spec C))` in `Over (Spec C)`. Its underlying scheme
morphism `g` satisfies `g ≫ 𝟙 = X.hom` (`Over.w`), so `g = X.hom`. Two such
morphisms are then equal by `Over.OverMorphism.ext`.

## `properSchemeLocalPointCompactness_of_properness`

Let `K` be a field with a topology such that `IsTopologicalDivisionRing K`,
`T2Space K` and `LocallyCompactSpace K` hold, and let `hnd : ¬ DiscreteTopology K`.
Then `SchemePointLocalPropernessProperty K hnd` implies
`ProperSchemeLocalPointCompactnessProperty K hnd`. The field `K` and `hnd` are
explicit arguments: `properSchemeLocalPointCompactness_of_properness K hnd h`.

Proof as implemented. Let `X : Over (Spec K)` have `IsProper X.hom`, and set
`Y = Over.mk (𝟙 (Spec K))`. The structure morphism gives `f = Over.homMk X.hom :
X ⟶ Y` with `f.left = X.hom`, so `f.left` is proper. Properness of `X.hom` supplies
the finite type, quasi-compactness and separatedness instances for `X.hom`
through Mathlib's instances. The identity `Y.hom = 𝟙` has all three by Mathlib's
instances for identities. The hypothesis then says that composition with `f` is
a proper map `RingPoint K X K → RingPoint K Y K` for the scheme point topologies.
By `subsingleton_hom_over_id`, `RingPoint K Y K = (ringTest K K ⟶ Y)` is a
subsingleton, so its `univ` is compact (`Set.Subsingleton.isCompact`). Preimages
of compact sets under a proper map are compact (`IsProperMap.isCompact_preimage`).
The preimage of `univ` is definitionally `univ`, so `RingPoint K X K` is a compact
space.

This is the standard derivation of the absolute compactness consequence from the
relative statement: a proper scheme over `K` is a proper morphism to the point
`Spec K`. It is internal to the proof route.
