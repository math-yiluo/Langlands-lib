# Full character-lattice labels for pinned comparisons

This internal construction supports the derived pair form of the pinned
classification. Its source context is Conrad, *Reductive group schemes* (2014),
Theorem 6.1.17 (p. 197) and the all-test argument for Theorem 7.1.9(3)
(pp. 245–246), registered as `conrad-2014-reductive-group-schemes`.
It uses the Library's fixed-comparison existence and uniqueness results with
`AffinePinnedIsomorphismTheoremStatement` retained as an explicit premise.

For two supplied affine pinned models, `ComparisonLabel` is the subtype of full
integral character-lattice equivalences admitting a based root-datum witness
and standard coordinate pairings. The witnesses are propositions. Thus label
equality records only the full lattice equivalence, including central directions.
No existence assertion for this subtype is built into its definition.

Each label selects the existing canonical fixed comparison on every common
scheme. Its exact torus action and fixed pinning equations are inherited from
that comparison. The standard pairings and based witness give its cocharacter
equation by `BasedCoordinateIso.cocharacter_comp`. This proves the concrete
`IsLocallyPinned` predicate. Fixed-comparison uniqueness supplies compatibility
with arbitrary pullback.

Cocharacter preservation implies canonical Borel preservation by transporting
the represented dynamic parabolic along the actual group isomorphism.

Equality of two representatives over a pointed common scheme forces equality
of labels: pull back to the residue field at the supplied point, cancel the
monic target torus inclusion, and compare all fixed-exponent characters.
The field character-lattice equivalence detects the full weight map. The proof
uses no connectedness or reducedness assumption on the original scheme. It
makes no uniqueness assertion for labels over the empty scheme.

`PreservesCocharacter.preservesBorel` is reused from `AffinePinnedAutomorphismSplittingGeometry`.
