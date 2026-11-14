# Membership in the successor principal-unit subgroup

This proves `Langlands.NYLL.CyclicCohomology.mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iffStatement`
with the required theorem `mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff`.
For any field `L` with a valuative relation and subgroups `Vsucc ≤ Vn` of
`𝒪[L]ˣ`, an element of `Vn` belongs to the successor subgroup exactly when its
underlying unit belongs to `Vsucc`. No local-field or normal-basis premise is used.

The proof unfolds the published proposition and the successor subgroup, then
applies Mathlib's `Subgroup.mem_subgroupOf`. The only import is the published
`NormalBasisLattice.U109.Statements` module; no unpublished helper is used.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 2002–2007,
unit M144.109. Registered source `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The implemented proof follows the original proof. Worker 517 extracted the unit,
prefixed its namespace with `Langlands.NYLL`, reduced imports and expressed its
type using the independently published proposition. The original copyright and
author header are retained; Apache-2.0 LICENSE and NOTICE remain in `licenses/NYLL/`.
