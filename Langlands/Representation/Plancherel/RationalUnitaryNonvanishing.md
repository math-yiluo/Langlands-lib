# Nonvanishing at actual unitary unramified characters

This internal derived module restricts the actual algebra of unramified
regular functions to the actual unitary unramified subgroup, proves that
restriction injective, and deduces simultaneous nonvanishing of finitely
many nonzero regular functions at a unitary parameter.

The group is any connected reductive group scheme over a nonarchimedean
local field, in arbitrary characteristic. Its rational points carry the
canonical rational-point topology. The construction retains all rational
norm characters and their existing continuous-character spaces. The
finite family of regular conditions can have an independent index universe.

## Provenance and implemented argument

This is derived polynomial algebra using the published
`finiteLaurent_eq_zero_of_eval_on_box`,
`rationalUnramifiedLaurentAlgebraEquiv_eval`,
`rationalCanonicalUnitaryUnramifiedCharacterCoordinates` and
`rationalCanonicalUnitaryUnramifiedCharacterCoordinates_coe`.
It makes no new assertion from external literature.

`infinite_range_circleToUnits` shows that the unit circle gives infinitely
many complex units, using its argument-coordinate equivalence with
`(-π, π]`. If a finite Laurent polynomial vanishes at every circle tuple,
the published infinite-box uniqueness lemma forces it to be zero. This
includes the rank-zero case.

`rationalUnitaryRegularRestriction` is the complex-algebra homomorphism
that evaluates an actual unramified regular function on a unitary
unramified character, forgetting only its unitary membership.
The complex and unitary coordinate comparison shows that evaluating a
Laurent polynomial after this restriction equals its usual Laurent
evaluation at the corresponding circle tuple. Infinite-box uniqueness
therefore proves `rationalUnramifiedRegular_eq_zero_of_unitary`, and
applying it to a difference proves restriction injective.

Every nonzero actual regular function consequently has a nonzero value
at some unitary character. For finitely many such functions, the published
unique-factorization result supplies cancellation and absence of zero
divisors in the actual regular algebra. Their product is nonzero.
Nonvanishing of its restriction gives one unitary character at which all
factors are nonzero. An empty family is allowed.

## Consumer boundary

This module does not identify Weyl stabilizers, prove that bad conjugacy
loci satisfy proper regular equations, establish regularity of a twist,
or prove any Jacquet multiplicity, induction unitarity, admissibility or
irreducibility theorem. A consumer selecting a regular unitary twist must
still construct its finite nonzero regular conditions and prove that their
nonvanishing implies regularity for the actual representations in question.
