# A finite lower set as a support-filtration tail

Worker 154. Internal geometric prerequisite for Renard VII.3.3. The module
constructs an open-prefix orbit ordering whose final block consists exactly
of any given Bruhat lower set. It uses actual double cosets and the existing
finite orbit-closure/refining-order interface. Both complementary blocks are
sorted in reverse order, and downward closure excludes a reversed relation
between the blocks. Finite lower class sets are closed, so all prefixes of
the resulting orbit order are open. The block boundary is precisely the
complement of the given lower set on the actual inducing quotient.

This is an implementation lemma derived from Renard VII.3.1–VII.3.3
(9 July 2026 version, printed pp.232–235), not a separately asserted source
result. It makes no representation-theoretic or finite-length claim.

`orderedDoubleCosetsOfAntitone` turns a representative map and an antitone
finite class enumeration into `OrderedDoubleCosets`. The representative
convention is the inverse of the supplied group point. Its prefix of length
`k` is the complement of the classes whose index is at least `k`; the latter
set is closed by `isClosed_leftQuotientDoubleCoset_preimage`.
`orderedDoubleCosetsOfAntitone_class` records the resulting class map.

`exists_lowerSet_tail_ordering` assumes finitely many double cosets, a linear
order refining `BruhatLE`, a downward-closed class set `T`, and representatives
for every class. It enumerates the complement of `T` and then `T` using
`finSumEquivOfFinset`, sorting both blocks by the dual linear order. Within
a block, sortedness reverses every Bruhat comparison. A comparison from
the first block to the second would violate downward closure, and a
comparison in the other direction already respects the block indices.
The theorem returns the two block lengths `a,b`, an open-prefix ordering,
and an equivalence `Fin b ≃ T`. The prefix of length `a` is exactly the
complement of the preimage of `T`, and the classes at indices `a+i` are
exactly the values of that equivalence. No antisymmetry assertion beyond
the supplied refining order is assumed or proved.
