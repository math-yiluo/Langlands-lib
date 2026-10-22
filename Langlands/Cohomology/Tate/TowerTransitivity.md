# Transitivity of Tate subgroup maps

Original proof: Worker 45. Audit and documentation: Worker 25.

For `K ≤ H ≤ G`, the restriction theorem compares direct restriction with
restriction through `H`, using the actual group isomorphism `towerReindex`
to identify `K` with `K.subgroupOf H`. The corestriction theorem uses the
same identification in the other diagram. Both statements apply in every
integer degree and preserve the carrier universe.

The degree-zero cases are the representative and coset-norm formulas in
`TowerDefinitions`. For positive degrees, the proved embedding connecting
isomorphisms reduce the formulas by one degree. For negative degrees, the
augmentation connecting isomorphisms make equality detectable in the next
degree. Restriction and corestriction commute with the connecting maps of
the scalar-split sequences by `SplitTransfer`; group-coordinate reindexing
commutes with the same actual connecting maps by `ReindexNaturality`.
The second induction principle uses the shifts of the ambient coefficient
module and their proved invertibility after subgroup restriction.

The source is Serre, *Local Fields* (1979), Chapter VII, section 7,
printed pp. 118–119 (PDF pp. 124–125), and Chapter VIII, sections 1–2,
printed pp. 127–130 (PDF pp. 133–136). This module supplies the
dimension-shifting proof on Mathlib's actual Tate cohomology.
The exact tower formulas are derived from the cited normalization and
dimension-shifting principles; the Lean proof explicitly handles the subgroup
carrier identification. It assumes neither transitivity nor boundary
compatibility: it uses the proved scalar-split boundary lemmas only on the
canonical shift sequences, whose scalar splittings are already constructed.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
