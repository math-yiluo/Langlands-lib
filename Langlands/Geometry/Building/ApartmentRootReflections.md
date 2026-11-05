# Actual root reflections from the apartment axioms

This internal adapter imports the proved fixed-hyperplane theorem
`RootReflectionProof.hasRootReflections` and the actual action and Weyl-image
constructions. It removes the explicit `HasRootReflections` premise from
their applications. The field has arbitrary universe `u`; the group,
normalizer, apartment, root groups, coroot and action are the original
objects supplied by the building data.

For every supplied actual opposite factor pair of a nonidentity root
point, `normalizerAffineEquiv_reflectionElement` identifies its actual
affine action with the geometric reflection of its root-point functional.
This equality needs no apartment-axiom premise. Under the apartment
axioms, `isCoroot_reflectionCoroot` makes its actual quotient coroot an
`IsCoroot` witness for the affine-root system, and
`normalizerAffineEquiv_reflectionElement_eq_of_isCoroot` gives the action
using any such witness.

The apartment axioms alone also place the action of every supplied pair,
and hence the image of their generated actual normalizer subgroup, in
`W(Ψ)`. The definition `reflectionWeylHom` restricts the actual apartment
action to this subgroup and its codomain to `W(Ψ)`. Its coercion is
literally the original action; multiplication and identity compatibility
are inherited from that action.

The reverse image equality and surjectivity of `reflectionWeylHom`
retain the explicit assumption
`RelativeRoot.HasRankOneFactorization B.i`. The imported reverse-image
argument supplies each affine-root generator using an actual opposite
pair. The surjectivity proof rewrites membership in `W(Ψ)` using that
equality, then takes the actual normalizer element witnessing subgroup
image membership.

For parahoric building data, the corresponding conditional reverse
containment places `W(Ψ)` in the affine image of the actual normalizer
intersection with the supplied simply connected image. This reuses the
imported containment of all the actual pair products in that image.

The provenance is derived: the module applies published fixed-hyperplane
and conditional action results, restricts a group homomorphism, and
unpacks its image. It introduces no additional claim from external
literature. It does not prove actual pair existence, the upper containment
for the entire simply connected normalizer, or the affine
Iwahori–Tits statement.
