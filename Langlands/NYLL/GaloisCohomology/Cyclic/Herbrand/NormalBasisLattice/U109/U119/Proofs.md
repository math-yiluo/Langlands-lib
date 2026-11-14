# The identity class in a successor principal-unit quotient

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff`
proves the exact published proposition with suffix `Statement`. For a field
`L : Type u` with a valuative relation, subgroups `Vsucc ≤ Vn` of `𝒪[L]ˣ` and
`u : Vn`, its successor-quotient class is one exactly when its underlying unit
belongs to `Vsucc`. The explicit `L`, `hV`, `u` and implicit subgroup/instance
binders retain the source order. No local-field or normal-basis premise is used.

The proof unfolds the proposition and views the class in the concrete quotient
of `Vn` by its successor subgroup. Mathlib's `QuotientGroup.eq_one_iff` reduces
class equality to membership in the denominator. That denominator unfolds to
`Vsucc.subgroupOf Vn`, whose membership is exactly `Subgroup.mem_subgroupOf`.
The source's final use of M144.109 is expanded directly here, so the proof
imports no pending candidate and publishes no duplicate helper under a reserved
name. The only import is the published `NormalBasisLattice.U109.Statements`
module and its published transitive dependencies.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 2096–2104,
M144.119; the expanded membership proof is lines 2002–2007, M144.109.
Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Worker 517 extracted the proof, prefixed its namespace with `Langlands.NYLL`,
reduced imports, expressed its type using the independently published target
and expanded the final membership step. The original author/copyright header
is retained; Apache-2.0 LICENSE and NOTICE remain in `licenses/NYLL/`.
