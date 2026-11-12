# A special vertex in the apartment of available corrected KP data

`Langlands.BruhatTits.SpecialCompact.availableSpecialVertexExistence` proves
exactly `AvailableSpecialVertexExistenceStatement.{u}`, for arbitrary universe
`u`. It applies to every nonarchimedean local field, every connected reductive
group over that field, and every `KPBuildingAssignment` available for that group.
Its sole building premise is the published `IsAvailableFor` predicate.

Write `B := (𝔅.datum F G hG).base`. The proof projects availability through
`IsAvailableFor.affineRootSystem` and
`KPBuildingDatum.SatisfiesAffineRootSystemAxiom.apartmentAxioms`. The field
`isAffineRootSystem_affineRoots` gives
`AffineRootSystem.IsAffineRootSystemWithRankZero B.apartment.affineRoots`.

The accompanying helper module
`Langlands.Geometry.Building.SpecialPointExistence` proves
`AffineRootSystem.IsAffineRootSystemWithRankZero.exists_isSpecialPoint`.
Applied to these roots, it supplies `x : B.Apartment` with the actual
`AffineRootSystem.IsSpecialPoint B.apartment.affineRoots x` predicate.
Its proof chooses affine lifts of linearly independent simple derivative roots,
takes their common zero, and uses finite simple-root reflection descent to
establish specialness. Its paired Markdown describes the full implemented
construction and its Mathlib dependencies.

The existing Library theorem
`AffineRootSystem.isVertex_of_isSpecialPoint`, from
`Langlands.Geometry.Building.SpecialPointVertices`, proves that this same
point is a vertex. The pair of proofs is precisely the published
`KPApartmentData.IsSpecialApartmentVertex x` definition, so it gives the
required existential witness.

Relative rank zero is included: the generic existence proof covers the empty
root system, and the existing special-point-to-vertex theorem uses derivative
spanning to identify its facet with a singleton. There is no split,
quasi-split, tame, rank, or residue-characteristic restriction. The proof adds no
validity, building-existence, joint-basis, or unproved proposition premise.

This is the apartment specialization of KP Proposition 1.3.43(1)–(3).
The abstract existence proof uses a finite reflection-descent argument for
part (2); the vertex implication is reused from the Library. Availability and
the apartment axioms are hypotheses on supplied data throughout.

Sources:

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Definition 1.3.39,
  printed p.29 / PDF p.60, and Proposition 1.3.43(1)–(3), printed p.30 /
  PDF p.61. Registered source
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p.27:
  corrected Definition 4.1.26, already represented by `IsAvailableFor`.
  Registered source `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
