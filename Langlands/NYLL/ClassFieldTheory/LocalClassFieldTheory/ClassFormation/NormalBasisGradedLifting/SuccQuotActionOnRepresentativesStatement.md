# Galois action on representatives of a principal-unit graded quotient

This target states that the actual Galois action on a normal-basis principal-unit successive quotient sends the class of a representative to the class of its Galois translate. It uses the published restricted action on `Vn` and its published descended action on `Vn / Vsucc`.

## Pinned source and name map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGradedLifting.lean`, M154.003. The statement is at lines 103–114, with docstring at 101, `@[simp]` at 102 and proof at 115. The file SHA-256 is `c86a5154f1ba4d19d41079de279f16163f4c8044143370a3177033440af445ae`.

The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGradedLifting.lean>) is registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mkStatement` |

## Complete telescope and target

The source section variables at lines 30–35 are explicit binders of the definition, in the original order:

```lean
(K L : Type u)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

Both fields share universe `u`. The types are explicit; all displayed hypotheses are instance binders. Binding this complete effective telescope directly preserves the parameters that a source theorem includes automatically but a section-level `def` can otherwise omit. The original declaration binders follow unchanged:

```lean
(n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
(hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
(hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
  chosenNormalBasisPrincipalUnitSet K L (n + 1))
(sigma : Gal(L/K)) (u : Vn)
```

Thus `Vn` and `Vsucc` remain implicit, and the level, inclusion, carrier equalities, Galois element and representative remain explicit. There is no positivity hypothesis on `n` or topology hypothesis on `L`.

The body is exactly the source proposition. It first installs `chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n Vn hVn`, then `chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction K L n hV hVn hVsucc`. In that order of local instances, it equates `sigma` acting on `chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u` with `chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV (sigma • u)`. Both quotient and subgroup actions are the actual source constructions. The return type is `Prop`.

## Published prerequisites and modifications

The sole direct import, `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting.PrincipalUnitSuccQuotAction`, supplies M154.002 and imports the actual M145.006 restricted action, the successive quotient and quotient-map definitions, and the published proofs used in their constructions. Its quotient action uses the actual Galois stability proof at level `n+1`. No prerequisite proof is supplied by a statement or an added assumption.

Worker 197 extracted this focused target, prefixed the namespace with `Langlands.NYLL`, and changed the source theorem to a `Prop`-valued `def` with the suffix `Statement`. The original docstring, complete telescope, binder kinds and order, both local instances, actual objects and equation are retained. The original theorem proof and its `@[simp]` attribute are omitted; a proposition definition is not registered as a simplification theorem. Unrelated declarations and unused namespace openings are omitted. The file introduces no global instance and proves no theorem.

The original copyright, author and Apache-2.0 header is retained. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. A proof of this exact target belongs to a separate proof task. This statement alone establishes no equivariance for the lattice equivalence, cohomological lifting, class formation or reciprocity theorem.
