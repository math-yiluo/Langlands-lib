# Complementary products from integral-line support

Author: Worker 1530, Task 5495.

`IntegralLineComplementaryIrreducibilityReduction` is an internal reduction.
It assumes the published proposition `UnlinkedSocleProductIrreducibility` and
concludes that the actual normalized product of the determinant-power twists
`ν^α S` and `ν^(-α) S` is irreducible when `-1/2 < α < 1/2` and `α ≠ 0`.
Here `S` has positive rank and a supplied actual supercuspidal support multiset
`s`, and every member of `s` is an integral real-power twist of a common
cuspidal datum `ρ`. The two blocks use the uniform block shape of length two.
The field universe `uF` and representation universe `uV` are independent.

The support predicate already requires that `S` be irreducible, so a separate
irreducibility premise is unnecessary. The statement retains the general
unlinked-socle theorem as its only representation-theoretic premise beyond the
supplied support and its integral coordinates. It asserts no unitarizability.

Provenance: this is a derived adapter for the task's complementary-Speh argument,
using the published multisegment socle exhaustion, identification and uniqueness
of actual cuspidal support, and transport of support under determinant twists.
The two twisted supports have exponents `m + α` and `m' - α`. Their differences
cannot be integers, since `2α` is a nonzero real strictly between `-1` and `1`.
Thus their multisegment parameters have no linked segments across the two
factors, permitting application of the retained unlinked-socle premise.
This statement is broader than the Speh application but does not itself assert
`SpehComplementaryIrreducibility` or completion of Task 5495.
