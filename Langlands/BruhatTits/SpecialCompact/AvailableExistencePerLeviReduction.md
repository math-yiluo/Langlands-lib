# The per-Levi existence target from Bruhat–Tits availability

This module proves a conditional result only. The theorem
`availableSpecialMaximalCompactExistencePerLevi_of_bruhatTitsAvailability` has type

```lean
BruhatTitsAvailabilityStatement.{u} → AvailableSpecialMaximalCompactExistencePerLevi.{u}
```

Here `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement` is the published,
unproved proposition that some `KPBuildingAssignment` is valid in the sense of the corrected
Kaletha–Prasad Definition 4.1.26 (the availability part of KP Theorem 9.2.7).
`AvailableSpecialMaximalCompactExistencePerLevi` is the target of module
`Langlands.BruhatTits.SpecialCompact.AvailableExistencePerLeviStatement`. The module does not
prove the premise, so the theorem is not an unconditional existence result.

The definition
`availableSpecialMaximalCompactExistencePerLeviOfBruhatTitsAvailability` is the record
entry. It restates the theorem as a definition with the same implication as its type,
following the published `specialMaximalCompactExistenceOfBruhatTitsAvailability`.
It introduces no new mathematical assumption or construction.

## Implemented proof

The published theorem `availableSpecialMaximalCompact_perLevi_of_bruhatTitsAvailability`
(module `Langlands.BruhatTits.SpecialCompact.AvailableExistenceReduction`) takes the premise
and `F, G, hG, S, i, hi, ν` and returns exactly the body of the target at these arguments.
The proof introduces the binders of the target, including the four instance arguments of
`F`, and applies that theorem.

That published theorem obtains a valid assignment from the premise, rebases it at `(G, i)`
with `validAssignmentTorusRebasing`, and applies `specialMaximalCompact_of_based_valid`. The
latter supplies the apartment `D`, a special vertex `x` with the special compact properties
(`availableSpecialVertexExistence`,
`availableSpecialCompactProperties_of_omegaCompatibleApartment`) and, for each standard Levi,
an assignment rebased at `(M_J, Standard.leviTorusHom i ν J)` whose apartment has a point
related to `x` by `SpecialLeviRestriction` (`prescribedLeviSpecialVertex` and compact
maximality).

## Provenance

Derived content: this module packages the conclusion of the published theorem
`availableSpecialMaximalCompact_perLevi_of_bruhatTitsAvailability` as the published
proposition `AvailableSpecialMaximalCompactExistencePerLevi`. The mathematical
source comparison is inherited from those two modules; this wrapper adds no
source assertion. The underlying route is availability, followed by the special
vertex and compact subgroup results.

The implication holds at arbitrary universe `u`, without a restriction on
characteristic, residue characteristic, rank, splitness or ramification. The
unconditional target requires a proof of the availability premise; this
intermediate result does not prove the unconditional target.
