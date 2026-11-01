# Finite ambient rational covers from relative rational neighborhoods

Author: Worker 84.

This is an internal construction for the compactness step of the full
Gerritzen–Grauert proof. It retains actual rational presentations over the
original ambient algebra and the bounded restrictions from a represented
domain. It does not prove the existence of the local rational neighborhoods.

`Domain.RationalNeighborhood U x` stores an ambient chart `D`, an actual arrow
`D.toDomain ⟶ U`, and the assertion that the inverse image of `D.locus` in
`U.locus` belongs to the neighborhood filter of `x`. The neighborhood assertion
is relative to the domain; it does not require the ambient rational locus to
contain an ambient open neighborhood. The arrow ensures `D.locus ⊆ U.locus`
by the existing domain inclusion theorem.

`Domain.FiniteRationalCover U` stores the finite data required by the published
`Domain.FiniteRationalCoverStatement`: a natural number, charts indexed by its
`Fin` type, actual restrictions, and pointwise covering of `U.locus`.
`toFiniteCover` retains the existing full domain cover structure. `empty`
constructs the empty cover when the represented locus is empty.

`FiniteRationalCover.ofNeighborhoods` chooses a relative rational neighborhood
for each point. The existing compactness of `U.locus` gives a finite subfamily
through `CompactSpace.elim_nhds_subcover`. The construction reindexes the
finite set by `Fin` and carries its chosen charts and restrictions along that
equivalence. It uses neither injectivity of the representing spectrum map nor
any strictness, reducedness, nonzero, or valuation hypothesis. All base and
rational radii remain arbitrary positive real numbers.

The final theorem `finiteRationalCoverStatement_of_neighborhoods` applies that
construction at the full universe `u`. Its explicit hypothesis is the local
analytic input, so this theorem alone does not establish the unconditional
published proposition or complete the finite-cover task.

The construction follows the compactness argument in M. Temkin, *A new proof
of the Gerritzen–Grauert theorem* (2005), registered source
`temkin-2005-gerritzen-grauert`, PDF SHA256
`1948a0be381d7dd4d4b5166c9b00f2ffa903a30a6ee0ffd09f754a5e9ad9c334`,
printed/PDF p. 5, the first paragraph of the proof of Theorem 1.1; Theorem 3.1,
p. 8, extends the argument to arbitrary positive radii and trivial valuations.
The packaging as relative neighborhoods and explicit bounded arrows is an
internal adaptation to the Library's represented-domain definitions.
