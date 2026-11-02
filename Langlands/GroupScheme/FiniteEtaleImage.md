# Actual images of finite étale group schemes

This is an internal construction using the actual group schemes over an arbitrary
scheme, the finite étale morphism properties in the Library, open-immersion
factorization, and `GroupObjectDescent.grpObjOfMono`. No external source assertion
or representability assumption is introduced.

For a homomorphism `f : G → H` of group schemes whose two structure morphisms
are finite étale, its underlying scheme map is finite étale. Its image is
therefore open and closed. The open subscheme with that image has a closed
immersion into `H` and a finite étale structure morphism over the original base.
`image`, `projection` and `inclusion` construct the corresponding group scheme
and homomorphisms. The original map factors as their composite, as proved by
`projection_inclusion`. The projection is itself finite étale and surjective.

The unit factors through the image because `f` preserves the unit. Surjective
precomposition by this image projection, and by its map on the twofold fiber
product, proves that inversion and multiplication land in the open image.
Open-immersion factorization supplies the actual restricted operations. The
categorical restriction theorem proves all group laws by cancelling the
inclusion. Both the inclusion and the surjection are actual homomorphisms, and
their composite is the original homomorphism.

When the target group scheme is commutative, the image is commutative: the
commutativity equation follows by cancelling the monomorphic inclusion.
The projection is an effective epimorphism on underlying schemes, hence an
epimorphism over the base and on group schemes. `hom_ext` therefore detects
equality of homomorphisms out of the image by precomposing with the projection.
For any commutative group-scheme target, `inclusion_comp_eq_one_iff` states
that a homomorphism kills the image if and only if its composite with the
original map is trivial. Here `1` is the trivial homomorphism in the actual
pointwise Hom group.

These constructions use actual scheme morphisms and their open subschemes,
including nilpotents, and impose no field, reducedness, or connectedness
hypothesis on the base. The supplied source and target both have finite étale
structure morphisms. The construction does not supply a torsion subgroup of an
abelian scheme, a quotient by that subgroup, or an integral model of a rational
action; these remain subsequent obligations in the CM application.
