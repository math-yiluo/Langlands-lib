# Coordinates and degree-zero formulas for a subgroup tower

Original proof: Worker 45. Audit and documentation: Worker 25.

For subgroups `K ≤ H` of `G`, `towerReindex` (from `TowerReindex`) is the
isomorphism of actual Tate groups given by the canonical group isomorphism
`K ≃* K.subgroupOf H` and the identity on coefficients. This file proves
its connecting-map formula `towerReindex_delta` and its representative
formula `towerReindex_zeroClass` in degree zero, using
`ReindexNaturality`.

Restriction leaves a scalar splitting unchanged. The actual coinduced
replacement remains Tate-acyclic after both subgroup restrictions, as follows
by applying the proved coinduced coordinate isomorphism at each level.
Consequently the augmentation connecting map remains an isomorphism.

The degree-zero corestriction formula uses Mathlib's explicit bijection
`G/K ≃ (G/H) × (H/(K.subgroupOf H))`. Splitting the finite coset sum by this
bijection proves the norm factorization. The two degree-zero transitivity
formulas then follow on invariant representatives. The corresponding
all-integer transitivity theorems are separate proof obligations.

The source for the restriction and corestriction conventions is Serre,
*Local Fields* (1979), Chapter VII, section 7, printed pp. 118–119
(PDF pp. 124–125), with Tate extension conventions in Chapter VIII,
sections 1–2, printed pp. 127–130 (PDF pp. 133–136). The present coordinate
and finite-sum proofs are internal implementations on Mathlib's existing
objects. The tower norm identity is derived here by factoring the coset sum;
it is not a separately numbered theorem in these cited passages.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
