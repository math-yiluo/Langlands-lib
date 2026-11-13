# Successive normal-basis principal-unit and lattice quotient comparison

Worker 197 adapts the theorem target M153.005 of Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.

Source: `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/PrincipalUnitGraded.lean`,
section telescope lines 30–34, full unit lines 221–263 and target lines 221–236.
The [pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/PrincipalUnitGraded.lean>)
is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Adapted declaration |
| --- | --- | --- |
| M153.005 | `LocalClassFieldTheory.exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot` | `Langlands.NYLL.LocalClassFieldTheory.exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuotStatement` |

There is a uniform natural-number bound `c` such that, for every `n ≥ c`,
there are actual subgroups `Vn` and `Vsucc` of `𝒪[L]ˣ` with the normal-basis
principal-unit carriers at levels `n` and `n + 1`, respectively, and a containment
`hV : Vsucc ≤ Vn`. Their successive quotient admits a multiplicative equivalence
`Φ` with the multiplicative form of the actual additive lattice quotient
`chosenNormalBasisLatticeSuccQuot K L n`. The subgroup `Vn` lies in
`principalUnits L 1`. For each `u : Vn`, the equivalence takes its quotient class
to the lattice class represented by `u - 1`, with subtraction in `𝒪[L]` followed
by coercion to `L`.

The order of the existential witnesses and conjunction is the source order:
`c`, all `n ≥ c`, `Vn`, `Vsucc`, `hV`, `hVn`, the successor carrier equality,
then `Φ`, the containment in `principalUnits L 1`, and its representative formula.
In that formula, `by exact hVn ▸ u.2` transports the actual subgroup membership
to the required normal-basis carrier membership. This proof term is preserved.
No equivalence, subgroup or containment is supplied as an additional hypothesis.

The complete source telescope is explicitly bound in the paired Lean file:

```lean
(K L : Type u)
[Field K]
[Field L]
[Algebra K L]
[FiniteDimensional K L]
[IsGalois K L]
[ValuativeRel K]
[TopologicalSpace K]
[IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[TopologicalSpace L] [IsNonarchimedeanLocalField L]
[Module.Finite 𝒪[K] 𝒪[L]]
```

The fields share the source universe `u`. The final three instances are the
source theorem's own binders. The source `omit` command at line 36 applies only
to its following theorem M153.001; it does not remove valuation compatibility
from M153.005. Explicit binding retains hypotheses which the extracted `Prop`
body does not itself use. The unused-variable linter is disabled only for this
definition.

The focused imports reuse published constructions by Lean name:

- `NormalBasisLattice.U102.Definitions` supplies
  `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitLatticeClass`
  and imports the actual normal-basis principal-unit carrier and lattice quotient.
- `NormalBasisLattice.U108.Definitions` supplies
  `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuot` and
  `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotMk`.
- `PrincipalUnits.Definitions` supplies
  `Langlands.NYLL.LocalFieldTheory.principalUnits`, the actual subgroup of
  integer units defined by maximal-ideal-power membership of `u - 1`.

Modification record: prefix the namespace with `Langlands.NYLL`; replace the
source theorem and its proof by a `Prop`-valued `def` with suffix `Statement`;
write the complete effective telescope explicitly; replace umbrella imports by
the focused published modules above; and omit unrelated declarations. The target
expression, binder order and kinds, quotient objects and representative proof
term are unchanged. The original copyright, author and Apache-2.0 header are
retained; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

This contribution states M153.005. It supplies no proof of that target and
establishes no class-formation or reciprocity theorem.
