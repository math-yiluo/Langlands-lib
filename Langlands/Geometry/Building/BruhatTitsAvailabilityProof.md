# Bruhat–Tits availability over nonarchimedean local fields

`Langlands.Geometry.Building.bruhatTitsAvailability` proves
`BruhatTitsAvailabilityStatement.{u}` for arbitrary `u`. One
`KPBuildingAssignment` for the connected reductive groups over nonarchimedean
local fields of either characteristic satisfies `IsValid`, which includes
all ten axioms of corrected Kaletha–Prasad Definition 4.1.26.
[Statement](BruhatTitsAvailabilityStatement.md)

## Proof

The Lean term applies `bruhatTitsAvailabilityReduction` to
`groupAxiomsExistence`. The latter supplies a datum satisfying the one-group
clauses for each group. The reduction chooses such a datum for each field and
group by `Classical.choose`. [One-group existence](GroupAxiomsExistenceProof.md)

The reduction uses `KPBuildingAssignment.isAvailableFor_iff` to combine the
one-group clauses with the comparison clauses. It obtains the central
surjection, derived subgroup and simply connected cover comparisons of
Axiom 4.1.1 from `buildingComparisonAxiom`, and the valued-field and group
isomorphism comparison of Axiom 4.1.17 from `isomorphismCompatibilityAxiom`.
Both results apply to the valuation-building data selected by the assignment,
so the reduction proves `IsValid` for that assignment.
[Reduction](BruhatTitsAvailabilityReductionProof.md)

This existence conclusion is the corrected Definition 4.1.26 part of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 9.2.7
(printed p. 329, PDF p. 360), in its local-field formulation. The axiom list
is the one on PDF p. 27 of the authors' 1 November 2024 corrections.
