# Faithful flatness of dominant group homomorphisms

`DominantHomFaithfullyFlatStatement.{u}` says the following for every field
`k : Type u`. Let `G` and `H` be actual affine group schemes over `Spec k`, with
`G` locally of finite type and `H` smooth over `k`. A schematically dominant
homomorphism `f : G → H` is flat and surjective.
`dominantHomFaithfullyFlat` proves this proposition. There is no perfectness,
connectedness or characteristic assumption, and the kernel is not assumed smooth.

This is a derived helper for the normal-subgroup quotient construction. Its
provenance is the published `DominantHomFlat.flat_of_isDominant` theorem, the
closed-point and flat-morphism results in Mathlib, and the published stalk
flatness descent `DominantHomFlat.flat_stalkMap_of_comm`. The earlier
`DominantHomFlat` module proves flatness by generic flatness and translations by
families of group points. Its separate surjectivity theorem assumes an
irreducible target. The present module supplies surjectivity without that
irreducibility premise. It does not assume a normal-subgroup quotient theorem.

The implemented proof first works over an algebraically closed field. A flat,
locally finitely presented morphism is open. To lift a rational target point
`b`, take the inverse translate of the open topological image and use dominance
to find a source point mapping into it. Choose a closed point in that nonempty
source open. Its image and its translate are rational points. A rational point
in the topological image has a rational lift: choose a closed point in its
nonempty closed fibre. The group identity then writes `b` as the image of a
quotient of two rational source points. Thus `f` is surjective on rational
points. Every target point specializes to a closed point, and the generalizing
property of a flat morphism lifts this specialization, proving topological
surjectivity.

For an arbitrary field, the proof base changes the actual homomorphism to an
algebraic closure in the same universe. Smoothness makes the base-changed target
reduced. Schematic dominance persists under this flat base change. Local finite
type over the noetherian target gives local finite presentation. The published
flatness theorem and the preceding rational-point argument yield flatness and
surjectivity after base change. Flatness descends on stalks along the flat
surjective source projection; surjectivity descends through the commuting
pullback square.

`AffineHomImage.projection_geometry` applies this result to the original
schematic-image projection from `AffineHomImage`. For a homomorphism between
affine groups with smooth source and locally finite type target, it proves that
the actual image group is smooth and its projection is flat, surjective, locally
of finite presentation and quasi-compact. It retains the original factorization.
This module supplies the geometric cover step; constructing a homomorphism with
a prescribed normal kernel remains a separate obligation.
