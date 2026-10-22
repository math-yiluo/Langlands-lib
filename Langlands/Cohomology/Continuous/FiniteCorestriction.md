# Finite-stage corestriction

Author: Worker 22. The construction imports the published
`QuotientSubgroupCohomology` and `Tate.CohomologyTransfer` modules.
Worker 45's ordinary-transfer construction is used as a dependency.

For a representation `A : Rep k G`, a normal subgroup `N`, and a subgroup
`H` containing `N`, `quotientCorestriction A H N hNH q` is the composite
of `quotientSubgroupCohomologyIso` with
`Langlands.Tate.ordinaryCohomologyCorestriction` for the actual image
subgroup `H.map (QuotientGroup.mk' N)` of `G/N`. Its source is ordinary
cohomology of `H/(N.comap H.subtype)` with the actual subgroup-fixed
coefficients, and its target is ordinary cohomology of `G/N` with `A^N`.
The finite enumeration required by ordinary corestriction is of the
coset space of this image subgroup. No transfer law is assumed.

For a compact topological group, an open subgroup `H`, and an open
normal subgroup `N ≤ H`, `finiteCorestriction A H N hNH q` specializes
that construction to the published `finiteQuotientRep` objects.
Compactness and openness give a finite quotient `G/N`; consequently
its coset space by the image of `H` is finite. The implementation
supplies `Fintype.ofFinite` to the ordinary transfer. All cohomological
degrees are natural numbers, including zero, and the common universe
`u` is arbitrary. The coefficient ring is an arbitrary commutative
ring; topology on coefficients is unnecessary at this finite stage.

The composite uses the actual cohomology maps: the first factor is
induced by the explicit quotient and coefficient equivalences, and the
second is the homology map of Worker 45's standard-resolution relative
trace cochain map. Those two underlying constructions supply the
intrinsic certificates. This pair does not assert refinement
compatibility, transitivity, coefficient naturality, or the index law.
In particular it does not yet define continuous corestriction.

Provenance is derived from Serre, *Local Fields*, Greenberg translation
(1979), Chapter VII, Section 5, printed pages 115–116 / PDF pages
121–122 (compatible maps and quotient fixed coefficients), Section 7,
printed pages 118–119 / PDF pages 124–125 (finite-index corestriction),
and Chapter X, Section 3, printed page 154 / PDF page 160 (the
inflation-indexed quotient system). These specific transports are
implementation infrastructure, not verbatim interfaces from Serre.
Literature ID `serre-1979-local-fields`; source SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
