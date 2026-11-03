# Commutative derived subgroups and perfect triviality

This internal unit works over an arbitrary base scheme in universe `u`.
It derives the results directly from the published full scheme-theoretic
derived-subgroup intersection and the represented identity subgroup. No
field, finite type, smoothness, connectedness or reductivity hypothesis is used.
The ambient group is separated and commutative as an actual group object.

`derivedSubgroup_eq_bot_of_isCommMonObj` proves that its derived subgroup
functor is the identity subgroup on every test scheme. The identity section
is closed by separatedness, and every commutator is the identity by
commutativity. The identity section is consequently an admissible subgroup
in the intersection defining the derived subgroup. Minimality gives one
inclusion; every subgroup contains the identity, which gives the other.

`IsDerivedSubgroup.commSourceIsoTrivial` identifies the source of any actual
derived-subgroup inclusion with the actual trivial group scheme over the
same base. It applies the published uniqueness isomorphism between two
representatives of the same all-test subgroup functor, using the identity
section as its second representative. Thus the conclusion retains the
whole scheme structure, including tests with nilpotents.

`commutativePerfectIsoTrivial` specializes this construction when the full
derived subgroup functor equals the whole group functor. This explicit
equality expresses perfectness without introducing a separate convention.
The identity morphism then exhibits the derived subgroup, so its source is
isomorphic to the trivial group scheme.

These are elementary prerequisites for an argument that a quotient which
is both commutative and perfect is trivial. This file does not construct
such a quotient, prove perfectness of semisimple groups, or assert central
generation for a reductive group.

Authorship: Worker 1367. Worker 1044 suggested the commutative-perfect
quotient application as a focused prerequisite.
