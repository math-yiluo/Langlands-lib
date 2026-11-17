# Nonzero invariant pairings on irreducible cuspidal realizations

This internal helper for Task 7294 reduces the requirements on a prospective
contragredient pairing. It derives its assertions from the existing actual
operator realizations, the published contragredient comparison lemmas, the
published existence of an actual irreducible cuspidal contragredient, and
Schur's lemma. It imposes no condition on the universe of the number field.
It does not construct a nonzero invariant pairing or identify the
inverse-transpose realization as a contragredient.

First, a complex-linear map commuting with the real Lie algebra actions
commutes with the genuine enveloping actions. The proof lifts an enveloping
element to the tensor algebra, extends real Lie covariance to the
complexification by tensor induction, and uses scalar, addition and
multiplication induction. Combining this fact with the existing finite
and compact generator criterion constructs a full-operator intertwiner.
No bijectivity assumption on this map is needed.

For every invariant pairing between actual operator realizations `S` and
`T`, its partial map `B.flip` intertwines the finite and compact actions
with their dual actions. Every vector of `T` is smooth for the finite
adelic group and finite for the standard compact at infinity. Mapping
these two properties through the partial map proves that each `B.flip x`
is a contragredient functional of `S`.

Suppose `T` is irreducible and an irreducible realization `D` of the
contragredient of `S` is available. Its contragredient pairing `C`
identifies `D` with all contragredient functionals of `S`. The automatic
functional property therefore factors `B.flip` through `C.flip` as a
linear map `L : T.Space → D.Space`. The published pairing-comparison
identities show that `L` commutes with the finite, compact and real Lie
actions; the first helper upgrades this to a full-operator intertwiner.
If `B` is nonzero, then `L` is nonzero. Schur's lemma makes it bijective.
Injectivity and surjectivity of `C.flip` then establish precisely the
remaining conditions of `IsContragredientPairing S T B`.

For actual irreducible cuspidal realizations of rank `r + 1`, the published
`cuspidalContragredientExistence` supplies `D`. Consequently any nonzero
invariant pairing between two such realizations is a contragredient
pairing, and its existence suffices for `T.IsContragredientOf S`.
The proper constant-term hypothesis remains the existing
`CompactSpace (AdeleQuotient F)`. The nonzero invariant pairing itself is
an explicit premise, so this criterion does not complete Task 7294.

`CuspidalNonzeroInvariantPairingCriterionStatement` packages this conclusion
as a proposition over every field universe;
`cuspidalNonzeroInvariantPairingCriterion` proves it by the construction above.
