# Proof of Tate subgroup-tower transitivity

Original proof: Worker 45. Audit and documentation: Worker 25.

`Langlands.Tate.towerLaws` proves exactly `TowerLaws` in arbitrary universe
`u`, assembling the two all-degree theorems of `TowerTransitivity`.
Their degree-zero cases are invariant inclusion and the iterated coset norm.
The scalar-split connecting laws for subgroup maps and the connecting
naturality of reindexing propagate the identities to every integer degree
through the canonical shift isomorphisms.

The transport is the actual `towerReindex` specified by the proposition,
with unchanged coefficient elements. The closing theorem has type
`Langlands.Tate.TowerLaws.{u}` without extra parameters or hypotheses.
It covers arbitrary commutative coefficient rings, finite groups and subgroup
towers, with all of the target's explicit finite-type instances. It requires
neither normality nor any restriction on the integer degree.

`TowerTransitivity.md` describes the two induction arguments, and
`TowerStatement.md` records the proposition's provenance. The supporting pairs
are `ReindexNaturality`, `ShiftInduction`, `TowerDefinitions`, and
`TowerTransitivity`; the transfer boundary helpers are imported separately
from `SplitTransfer`. All operations and connecting maps are the published
constructions on Mathlib's actual Tate cohomology.

The mathematical normalization and dimension-shifting method come from Serre,
*Local Fields* (1979), VII §7, printed pp. 118–119 (PDF pp. 124–125),
and VIII §§1–2, printed pp. 127–130 (PDF pp. 133–136).
The tower identities, coefficient-coordinate maps and induction proofs here
are internal derivations of those principles. Source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
