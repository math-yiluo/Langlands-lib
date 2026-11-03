# Actual subrepresentation sums and irreducible subquotients

This is an internal algebraic supporting unit for the full smooth support
category arguments. It constructs the actual inclusion between ordered invariant
subrepresentations, the inverse image of an invariant subrepresentation along
an intertwiner, and the restricted map to that inverse image.

The implemented constituent argument uses the published actual binary
subquotient dichotomy, not a finite-length or Grothendieck-group replacement.
For a binary sum, the quotient by the first summand is a quotient of the second
summand. Finite induction gives the finite-sum assertion. For a nonempty
directed sum, a nonzero vector in the irreducible quotient lifts to a vector
whose image belongs to one member. Restriction to that inverse image gives a
nonzero, hence surjective, map to the irreducible quotient. Finally, the finite
partial sums form a directed family with supremum the original arbitrary sum.
The empty index family is included.

The coefficient field, group, carrier, and indexing universes are independent.
No local compactness, admissibility, finite length, or existence of categorical
coproducts is assumed. Sums are the actual invariant-submodule suprema in a
fixed ambient smooth representation.

The principal published dependencies are
`SmoothRep.irreducibleSubquotient_dichotomy`,
`SmoothRep.isSubquotient_iff_exists`,
`smoothSubquotientTransitivity`, and
`Langlands.Subrepresentation.toSubmodule_iSup`. The first two are reached
through a module that also contains GL-specific supercuspidal-support
definitions; this proof uses only their general actual-subquotient algebra.
It invokes no classification, geometric-lemma, adjunction, or character
independence result.
