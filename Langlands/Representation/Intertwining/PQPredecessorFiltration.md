# The regularity quotient filtered by strict predecessor pieces

Worker 154. Derived geometric prerequisite for Renard VII.3.3 (9 July 2026,
printed pp.234–235 / PDF pp.240–241). The quotient is the original quotient
by the boundary-support image at the identity. Its filtration has one grade
for each actual double coset strictly below the identity. Each grade is
naturally isomorphic, with the original target Levi action, to the full
geometric piece for the supplied representative and intersection datum.

The proof places the strict predecessor lower set at the end of an open-prefix
orbit order and changes representatives to the supplied points without changing
any orbit or prefix. Prefix preservation uses the shared
`initialOrbits_replaceRepresentatives` theorem from `OrbitRepresentatives`. It identifies the boundary support with the prefix at
the block boundary, then applies the quotient-tail construction. Exact target
coinvariants identify each surviving support grade with its compact orbit
model, and the published local normalized orbit comparison identifies that
model with the requested geometric piece. The final equivalence of index sets
is complete, including when the strict predecessor set is empty.

The result uses the original local-field and reductive hypotheses and makes
no admissibility or finite-length assertion.

`pqRegularityPieceFiltration` packages this construction as data: the length,
the equivalence with all strict predecessors, the actual quotient filtration,
and chosen natural isomorphisms from its grades to the supplied pieces. It
chooses these data from the proved existence theorem; no further premise is
required. The choices have no asserted uniqueness.
