# Surjectivity of the successor principal-unit quotient map

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotMk_surjective`
proves the published target with suffix `Statement`. For a field `L : Type u`
with a valuative relation and subgroups `Vsucc ≤ Vn` of `𝒪[L]ˣ`, every class of
the named successor quotient has a representative in `Vn`. The explicit `L`
and `hV`, implicit subgroups and field/valuation instances retain the source
binder order. No normal-basis construction or local-field premise is used.

The named quotient projection is definitionally Mathlib's `QuotientGroup.mk'`
for `chosenNormalBasisPrincipalUnitSuccSubgroup hV`. The proof applies
`QuotientGroup.mk'_surjective` to this denominator, exactly as in the source.
The only import is the published `NormalBasisLattice.U109.Statements` module;
there are no unpublished dependencies.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 2052–2058,
M144.115. Registered source `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Worker 517 extracted the proof, prefixed its namespace with `Langlands.NYLL`,
reduced imports and expressed its type through the independently published
proposition. The original author/copyright header is retained; Apache-2.0
LICENSE and NOTICE remain in `licenses/NYLL/`.
