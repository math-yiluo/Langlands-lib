# NYLL M043.011: `rep_norm_eq_generatorIterateSum`

Worker 747, 16 November 2026. The norm of a finite cyclic representation is the sum of the first `n` iterates of any map agreeing pointwise with the generator action.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.rep_norm_eq_generatorIterateSumStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.rep_norm_eq_generatorIterateSum`. The theorem's conclusion is that exact target applied to all of
its parameters, with the source binders, binder kinds and implicit group
argument unchanged. The target's Lean/Markdown pair and its imports are
unchanged.

## Statement

For a finite group `Q : IntegralRepGroupType`, `B : Rep ℤ Q`, `g` with
`hg : ∀ q, q ∈ Subgroup.zpowers g`, `n` with `hcard : Fintype.card Q = n`, a
function `f : B.V → B.V` with `hf : ∀ z, B.ρ g z = f z` and `x : B.V`, the
theorem proves `B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x`.

## Proof

After unfolding the target:

1. The private lemma `rep_norm_eq_generatorPowerSum_local B g hg n hcard x`
   rewrites `B.norm.hom x` to `∑ i : Fin n, B.ρ (g ^ i.1) x`.
2. `Finset.sum_congr rfl` reduces the equality of sums to the termwise
   equalities `B.ρ (g ^ i.1) x = (f^[i.1]) x`.
3. The private lemma `rep_action_pow_eq_iterate_local` rewrites the left side
   to `((B.ρ g)^[i.1]) x`.
4. `funext hf` gives `⇑(B.ρ g) = f`; applying `congrArg (fun h => h^[i.1])`
   and evaluating at `x` with `congrFun` closes each term.

The two private lemmas have exactly the propositions of M043.009 and M043.010
and reproduce their source proofs (lines 220–253 and 257–261): the power-sum
lemma builds the bijection `Fin n ≃ Q`, `i ↦ g ^ i.1`, from
`orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq`,
`Nat.ModEq.eq_of_lt_of_lt` and `IsCyclic.image_range_orderOf`, and reindexes
the norm sum with `Equiv.sum_comp`; the iterate lemma fixes the instance
`Module ℤ B.V := B.hV2` and rewrites with `map_pow` and
`Module.End.coe_pow`. The published theorems
`Langlands.NYLL.ClassFormation.rep_norm_eq_generatorPowerSum` and
`Langlands.NYLL.ClassFormation.rep_action_pow_eq_iterate` were not yet in the
Library at this workspace base, so these arguments are kept local under
private, non-conflicting names; no second public copy is introduced.

This is the source proof of lines 265–275 (docstring 263–264) after the
leading `unfold`, with the source references to M043.009 and M043.010
replaced by the local lemmas.

## Dependencies

Imports: `Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic` and the published
target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`.
Mathlib facts used, besides those listed above: `Finset.sum_congr`,
`congrFun`, `congrArg` and `funext`.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 265–275 (docstring lines 263–264), with M043.009 at lines 220–253 and M043.010 at lines 257–261; ambient context lines 18–30; original file SHA-256
`5ac5450e039760193ab008f2bed81158a543d2d9982515cd2e376baeadfe1284`. Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources: `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
and `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Copyright 2026 Naganori Yamaguchi; original authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original copyright and author header is
retained in the Lean file together with an explicit modification record.
Adaptations: the namespace is prefixed by `Langlands.NYLL`; the theorem's
conclusion is stated as the published `...Statement` target applied to all
its parameters, and the proof begins by unfolding that target;
the source import closure is replaced by the published target module and the Mathlib cyclic-group module, and the unpublished prerequisites M043.009 and M043.010 are reproduced as the private lemmas described above.
The Apache-2.0 license and notices remain unchanged in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`, SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope and checking

The proof introduces no axiom, `sorry` or global instance; development
inspection reports only the standard axioms `propext`, `Quot.sound` and (where
classical choice is used) `Classical.choice`. This theorem asserts exactly the
stated proposition and discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
Development compilation does not constitute independent proof acceptance;
publication requires the proof policy's independent review, build and
exact-target checks.
