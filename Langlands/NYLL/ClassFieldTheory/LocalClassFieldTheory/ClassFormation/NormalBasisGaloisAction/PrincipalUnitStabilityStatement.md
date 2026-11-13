# NYLL stability of normal-basis principal-unit sets

Worker 197 adapts M145.005 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`,
lines 126–137 (target at 126–130, section variables at 92–94 and 120–122).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata entry was found in the Library.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSetStatement` |

The target says that the actual Galois action on valuation-ring units preserves
the set of units whose deviation from one belongs to the specified normal-basis
lattice dilate. The supplied membership premise `ha`, its implicit unit `a`, the
level `n` and the Galois automorphism `sigma` retain their source order and binder
kinds. The target retains the source `letI` installing the integer-unit action.

The universe is `u`. The complete effective source telescope is explicitly bound:
`(K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
[IsGalois K L] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K] [ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]`, followed by the original declaration's binders.
No ambient instance is omitted. Explicit binding preserves the theorem telescope
when changing the command to `def`; the unused proof parameter `ha` is retained
with a declaration-scoped unused-variable linter suppression.

The focused imports reuse `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet`
from `NormalBasisLattice.U059.Definitions` and
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`
from `ClassFormation.Valuation.IntegerDefinitions`. These are the actual source
carrier and integral-closure action. The imported set uses subtraction in `𝒪[L]`
and then coercion to `L`, exactly as in the source. No substitute carrier or
global action instance is added.

Modifications: prefix the namespace by `Langlands.NYLL`, append `Statement`,
extract this focused pair, replace broad imports with the published focused
imports, remove unused openings, and replace the theorem proof by its exact
`Prop`-valued target. No proof of this target is supplied. The original copyright
and author header is retained; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
apply. This target does not establish a class-formation or reciprocity theorem.
