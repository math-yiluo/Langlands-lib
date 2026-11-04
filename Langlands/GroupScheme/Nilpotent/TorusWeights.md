# Split-torus fixed Lie algebra in a nilpotent group

Author: Worker 1487.

This internal derivation identifies the zero character weight space of
any split torus mapping to a smooth connected affine geometrically nilpotent
group over a field with the group's full actual Lie algebra.
`IsNilpotentGroupScheme.splitTorusFixedLieEquiv` is the linear equivalence
given by inclusion of that weight space; its forward map is the original
submodule inclusion. No closedness or injectivity of the torus homomorphism
is needed. The field, torus, group and test algebras have arbitrary universe
`u`; the field can have any characteristic.

For a product of multiplicative groups, evaluate a weight vector at the
universal torus point over the group algebra of its integer exponent lattice.
The character value is its actual monomial. Thus the adjoint difference acts
on the extended vector by the monomial minus one. The previously constructed
geometric nilpotence bound makes that adjoint difference nilpotent over this
test algebra. Applying a vanishing power to the weight vector and then
evaluating its identity derivation on a coordinate gives a product equal to
zero. The group algebra is a domain, and a nonzero exponent has monomial
different from one, so the derivation value is zero. Injectivity of the
field's algebra map gives that the original vector is zero. This proves
vanishing of each nonzero character weight space.

Reparametrization by a splitting isomorphism proves the same conclusion for
any split torus. The published internal weight decomposition spans the full
Lie algebra. Since every nonzero weight space is zero, the zero weight space
is the full space, providing the asserted equivalence.

The argument uses the full character on an actual universal algebra point;
it does not require a nonzero differential of the character. It therefore
also detects nonzero characters divisible by the positive characteristic.
This is a derivation from the existing weight, adjoint, identity-derivation
and nilpotence constructions, without a new literature translation.
Centrality on the whole group, descent for nonsplit tori, and the central
maximal-torus quotient theorem remain separate obligations.
