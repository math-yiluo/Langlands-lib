# Finite-cover descent of discreteness for a supplied local lift

This internal lemma applies to a module sheaf on a twisted site with
admissible refinements. Suppose the local action system consists of lifts
and a section's discrete sieve contains a finite covering family. Then
the section is discrete for any supplied admissible action at its object.

Restriction equivariance for an arrow `f` between lifts identifies the
source group element with the image of the target element under
`inverseTwistConjugation f`, the group homomorphism given by conjugation by
the inverse twist. The proof takes the inverse image of an open source
subgroup under this homomorphism and intersects it with the target subgroup.
Restriction equivariance gives local equivariance in the other direction.

The witnesses in the discrete sieve factor the given finite covering family
through a finite covering family with discrete restrictions. The existing
`IsDiscreteSection.of_finite_family` applies to this family, using
separatedness of the sheaf. This extends the finite-cover argument of
`TwistedFiniteGlobalSections` from the twisted base to an object carrying
a supplied admissible lift.
