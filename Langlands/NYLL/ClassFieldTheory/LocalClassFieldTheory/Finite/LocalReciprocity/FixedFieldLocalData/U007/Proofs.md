# The decomposition group of the chosen valuation ring over a finite separable extension: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData.U006.Statements`,
source row M272.007) as the theorem

```lean
theorem localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv :
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement
```

in the namespace `Langlands.NYLL.LocalClassFieldTheory`. The statement says:
for a finite separable extension `F / K` of nonarchimedean local fields whose
valuation extends that of `K`, an embedding `i : F →ₐ[K] SeparableClosure K`
(making `SeparableClosure K` an `F`-algebra) and an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K`, every `F`-algebra
automorphism of `SeparableClosure K` maps the chosen valuation ring
`localSeparableValuationSubring K` onto itself, that is
`decompositionGroup F (localSeparableValuationSubring K) = ⊤`.

## Proof

The proof is the source proof, with the published Library names.

1. `intro K F _ _ _ _ _ _ _ _ _ _ _ _ i` introduces the two fields, their
   twelve instance hypotheses and the embedding `i`. The statement's three
   `letI` lines are inlined by Lean; as in the source, the proof restates
   them with `let`, with the same terms, and then introduces `e`.
2. With `A := localSeparableValuationSubring K` and
   `AF := localSeparableValuationSubring F`, the M272.006 theorem
   `localSeparableValuationSubring_eq_comap_finiteExtensionEquiv` gives
   `hAF : AF = A.comap e.toRingHom`, and the M249.010 theorem
   `localSeparableDecompositionGroup_eq_top` applied to `F` gives
   `hAFtop : decompositionGroup F AF = ⊤`.
3. By `top_unique` it suffices to show that every
   `sigma : SeparableClosure K ≃ₐ[F] SeparableClosure K` satisfies
   `sigma • A = A`. Let `sigmaF := AlgEquiv.autCongr e.symm sigma`, the
   conjugate automorphism of `SeparableClosure F`. By `hAFtop`,
   `sigmaF • AF = AF` (`hsigmaF`).
4. For each `x`, `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`
   turns `x ∈ sigma • A` into `sigma⁻¹ • x ∈ A`. The auxiliary fact
   `hmem z : e.symm z ∈ AF ↔ z ∈ A` follows from `hAF` and
   `e.apply_symm_apply`. Rewriting both sides with `hmem` gives
   `e.symm (sigma⁻¹ • x) ∈ AF ↔ e.symm x ∈ AF`. Applying the membership of
   `e.symm x` to `hsigmaF` and the same Mathlib lemma gives
   `sigmaF⁻¹ • e.symm x ∈ AF ↔ e.symm x ∈ AF`, and `simpa` with the
   definition of `sigmaF` and `AlgEquiv.autCongr_apply` identifies the two.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Library declarations used

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M272.007 statement | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement` (module `...LocalReciprocity.FixedFieldLocalData.U006.Statements`, imported through the M272.006 proof module) |
| M272.006, `LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquiv` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquiv` (module `...LocalReciprocity.FixedFieldLocalData.U006.Proofs`) |
| M249.010, `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (module `...LocalReciprocity.LocalResidueDatum.U010.Proofs`) |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (imported through the statement module) |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | as in the statement module |

The two imported modules are the M272.006 and M249.010 proof modules in
rows two and three. `decompositionGroup` is reached through
`open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
and the pointwise action through `open scoped Pointwise`. `top_unique`,
`AlgEquiv.autCongr`, `AlgEquiv.autCongr_apply`, `AlgEquiv.apply_symm_apply`
and `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem` are Mathlib
declarations.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean>)
(SHA-256
`e629ef932276f009cee72064f4b1dffe03aa262dcd391da5a6e98c4c9008f3cd`). The
M272.007 docstring occupies lines 260–262, its signature lines 263–281 and
its proof lines 282–326.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source proof:

- The theorem proves the published closed proposition instead of restating
  the signature, so it begins with `intro` for the quantified variables.
  The tactic steps after that are the source text.
- Names are prefixed with `Langlands.NYLL`, including the opened namespace
  `RamificationTheory.HilbertRamification.ValuationSubring`; the source's
  `open scoped Pointwise` is kept.
- The imports are the two published modules listed above. The other source
  declarations and `open` lines are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0 notice,
and records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files.
