# Cocenter torus quotient data from derived maximal-torus products

Author: Worker 1616.

`cocenterTorusQuotientData` constructs a commutative quotient torus `Q` and
`q : G ⟶ Q.toGrp` from a connected reductive group `G` over any field and
an actual derived subgroup `d : D ⟶ G`. It takes the published proposition
`DerivedMaximalTorusProductSurjectivityStatement` as an explicit additional
input. The universe is arbitrary.

The data retain smoothness and affineness of the structure morphism of `Q`,
the exact fppf quotient property with kernel `SubgroupFunctor.range d`, and
`IsTorus Q.toGrp`. For every specified maximal torus `t : T.toGrp ⟶ G`,
the composite `t ≫ q` is surjective as a morphism of schemes. For every
field extension `E/k` in the same universe splitting `T`, the quotient
`Q_E` is split as well. Integral cocharacter surjectivity is a separate
obligation and is not a conclusion of this construction.

The implemented construction starts with
`IsDerivedSubgroup.commutativeQuotientData`. The helper
`IsDerivedSubgroup.surjective_comp_of_surjective_product` applies the
annihilation theorem `IsDerivedSubgroup.comp_eq_one`: on `D × T`, the
composite of multiplication with `q` is exactly the second projection
followed by `t ≫ q`. Surjectivity of multiplication and of `q` therefore
implies surjectivity of `t ≫ q`. This argument uses scheme surjectivity;
it makes no claim that all rational points lift over the original field.

`IsSplitTorus.of_surjective_hom_to_smooth` uses reducedness of a smooth
field scheme to turn scheme surjectivity into schematic dominance, then
applies `IsSplitTorus.of_schematicallyDominant_hom`. The helper
`IsTorus.isSplitTorus_baseChange_of_surjective_hom` transports the
surjectivity through the actual pullback square of group schemes and
applies this split-image theorem. It does not require the source to be a
torus over the ground field: splitness over the supplied extension suffices.
Finally, maximal-torus existence and a splitting field of that torus give
the required splitting field witnessing `IsTorus Q.toGrp`.

This is an internal assembly of named Library constructions and the
explicit product-surjectivity proposition. It supplies a focused
conditional part of the cocenter existence proof; it neither proves that
product proposition nor identifies the kernel of `T → Q` as connected.
