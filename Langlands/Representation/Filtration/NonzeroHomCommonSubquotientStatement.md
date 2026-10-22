# A nonzero intertwiner gives a common irreducible subquotient

`Langlands.NonzeroHomCommonSubquotientTheorem` is an internal algebraic
prerequisite for the association theorem for cuspidal induction. It states that
two smooth representations over a field have a common actual irreducible
subquotient whenever there is a nonzero intertwiner from the first to the
second and the second is Artinian over the group algebra.

The field, group and two carrier universes are independent. The group has an
arbitrary topology. No finite dimensionality, admissibility, or finite length
of the source is assumed. Artinianness refers to the group algebra action,
not to the vector space over the coefficient field.

The conclusion uses four actual invariant submodules: a subrepresentation of
each ambient representation and an invariant submodule by which to quotient
each restriction. The first quotient is irreducible, and an equivariant linear
equivalence identifies it with the second. This is the literal existential used
in `Langlands.CuspidalSupport.CuspidalInductionAssociationTheorem`, and so it does
not require that the two carriers lie in a common universe.

This statement is derived internally from the elementary Artinian module
argument: a nonzero image contains a minimal nonzero submodule; its inverse
image in the source maps onto it. The first isomorphism theorem realizes the
result as actual subquotients. This file states the proposition only; it does
not assert a proof or import any analytic result about parabolic induction.
