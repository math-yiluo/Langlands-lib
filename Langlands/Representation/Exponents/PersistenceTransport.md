# Transport used in cuspidal-exponent persistence

This internal module proves unconditional transport identities needed for the
persistence proof. It does not assert the geometric lemma, a constituent
classification theorem, or persistence itself.

`isLeviQuasicuspidal_transport_of_conjugatesLevi` removes the minimality
restriction from the published whole-Levi transport theorem. The published
`minimalConjugatingCosets` theorem writes the given permutation as a minimal
conjugating permutation followed on the right by an element of the source
block Weyl group. The latter transport is inner and is intertwined with the
original representation by `transportWeylEquiv`. Quasicuspidality passes through
this equivalence and the minimal transport theorem. The transport composition
identity then returns the original permutation. Over a topological field,
`isLeviCuspidal_transport_of_conjugatesLevi` adds the existing admissibility
transport theorem. No irreducibility or positive rank assumption is needed.

For any two refinements `S, R` of one coarse shape `B`, and a permutation `h`
in `blockWeyl B` conjugating `B.flatten S` onto `B.flatten R`,
`leviRealPowerCharacter_restrictParameter_conjugation` identifies the restricted
coarse determinant characters under inverse Levi conjugation. The proof uses
the actual coarse Levi element associated to `h`, the injectivity of the
coarse Levi embedding, and the flattened embedding identity to express this
inverse conjugation as inner conjugation inside the coarse Levi. A character
into the commutative group of complex units is invariant under that inner
conjugation. The published refined character restriction then gives the
claimed equality in fine coordinates.

`transport_restrictedLeviRealPowerTwist` applies the character equality to the
actual actions, and `restrictedRealTwistTransportEquiv` is the resulting
identity on vectors as an intertwining equivalence. Finally,
`transport_nestedLeviRealPowerTwist` uses the published twist addition formula
to split `nestedParameter B S v t = restrictParameter B S t + (-v)` before
transport. It retains the same `h` and conjugacy witness throughout.

All results are derived from the cited Lean imports. This is internal algebraic
infrastructure, with no new original-literature assertion. The field and
representation-carrier universes remain independent.
