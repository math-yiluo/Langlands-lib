# NYLL finite-quotient boundary statements

Worker 197 adapts the units below from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean`.
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata entry was found in the Library.

| Unit | Original name in `LocalClassFieldTheory` | Source lines; target lines | Adapted name in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M148.001 | `exists_principalUnits_le_chosenNormalBasisPrincipalUnitSet` | 35–56; 35–38 | `exists_principalUnits_le_chosenNormalBasisPrincipalUnitSetStatement` |
| M148.005 | `exists_finite_chosenNormalBasisIntegerUnitsQuotient` | 95–111; 95–99 | `exists_finite_chosenNormalBasisIntegerUnitsQuotientStatement` |

At all sufficiently deep normal-basis levels the carrier contains an ordinary principal-unit subgroup, and every actual subgroup with that carrier has finite quotient in the integer-unit group.

M148.001 retains the high-level existential quantifiers, subset of the actual normal-basis carrier, and ordinary principal-unit group. M148.005 quantifies over every subgroup with that carrier and states finiteness of its actual group quotient. It retains the carrier equality as a proposition under the quantifier. Neither target assumes a chosen subgroup or a proof of the other target.

The common source section telescope is at lines 26–31. Both targets explicitly retain it in full, including finite dimensionality, the Galois hypothesis, both local-field topologies, the valuation-extension instance and finite generation of the extension integer ring. There is no source `omit` command for either declaration.

The explicit telescope of M148.001 (the concluding `Prop` body is the source target):

```lean
def exists_principalUnits_le_chosenNormalBasisPrincipalUnitSetStatement
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
    [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
```

The explicit telescope of M148.005 (the concluding `Prop` body is the source target):

```lean
def exists_finite_chosenNormalBasisIntegerUnitsQuotientStatement
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
    [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
```

The focused imports are the published modules:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`
- `Mathlib.GroupTheory.QuotientGroup.Basic`

They supply the actual normal-basis carriers, lattices and integer-unit operations used in these targets. No source proof needed only by the original theorem proof is imported or reproduced.

Modifications: prefix the namespace by `Langlands.NYLL`, append `Statement` to theorem names, extract this focused pair, replace broad source imports with the focused published imports, remove unused namespace openings and commands, and replace theorem proofs by their exact `Prop`-valued targets. Effective source theorem telescopes are explicit so that `def` does not drop ambient instances. Each declaration has a scoped unused-variable linter suppression to retain all named source premises and the full instance telescope even where the conclusion does not depend on them. Quantifiers, binder kinds, local instances and coercions in each target remain unchanged. No proof of any target or conflicting global instance is introduced.

The original copyright and author header is retained. The Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. These supporting statement families do not establish a class-formation or reciprocity theorem.
