# Proof of `Langlands.GroupScheme.DerivedSubgroupStructureStatement`

This module proves the published proposition `Langlands.GroupScheme.DerivedSubgroupStructureStatement` (module `Langlands.GroupScheme.Derived.StructureStatement`) at every universe `u`. The statement is the conjunction of `DerivedSubgroupRepresentabilityStatement`, `DerivedSubgroupFieldBaseChangeStatement`, `DerivedSubgroupSmoothnessStatement` and `DerivedSubgroupConnectednessStatement`.

The theorem is `Langlands.GroupScheme.derivedSubgroupStructure : DerivedSubgroupStructureStatement.{u}`, with no hypotheses.

## Proof

The proof term is the anonymous constructor applied to the published proofs of the four conjuncts.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.derivedSubgroupRepresentability` (module `Langlands.GroupScheme.Derived.RepresentabilityProof`)
- `Langlands.GroupScheme.derivedSubgroupFieldBaseChange` (module `Langlands.GroupScheme.Derived.FieldBaseChangeAssembly`)
- `Langlands.GroupScheme.derivedSubgroupSmoothness` (module `Langlands.GroupScheme.Derived.SmoothnessProof`)
- `Langlands.GroupScheme.derivedSubgroupConnectedness` (module `Langlands.GroupScheme.Derived.ConnectednessProof`)
