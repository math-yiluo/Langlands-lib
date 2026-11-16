# NYLL M043.009: `rep_norm_eq_generatorPowerSum`

Worker 747, 16 November 2026. The norm of a finite cyclic representation is the sum of the actions of the first `n` powers of a generator.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.rep_norm_eq_generatorPowerSumStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.rep_norm_eq_generatorPowerSum`. The theorem's conclusion is that exact target applied to all of
its parameters, with the source binders, binder kinds and implicit group
argument unchanged. The target's Lean/Markdown pair and its imports are
unchanged.

## Statement

For a finite group `Q : IntegralRepGroupType`, a representation
`B : Rep ℤ Q`, an element `g` with `hg : ∀ q, q ∈ Subgroup.zpowers g`, a
natural number `n` with `hcard : Fintype.card Q = n` and `x : B.V`, the
theorem proves `B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x`.

## Proof

After unfolding the target and entering `classical`:

1. `horder : orderOf g = n` follows from Mathlib's
   `orderOf_eq_card_of_forall_mem_zpowers hg`, `Nat.card_eq_fintype_card`
   and `hcard`.
2. The map `Fin n → Q`, `i ↦ g ^ i.1`, is shown bijective and packaged as an
   equivalence `e` with `Equiv.ofBijective`.
   - Injectivity: equal powers give `i.1 ≡ j.1 [MOD orderOf g]` by
     `pow_eq_pow_iff_modEq`; rewriting with `horder` and
     `Nat.ModEq.eq_of_lt_of_lt` with `i.2`, `j.2` gives `i.1 = j.1`, hence
     `i = j` by `Fin.ext`.
   - Surjectivity: `IsCyclic.image_range_orderOf hg`, rewritten by `horder`,
     says that the image of `Finset.range n` under `i ↦ g ^ i` is
     `Finset.univ`; every `q` is therefore some `g ^ i` with `i < n`.
3. `Equiv.sum_comp` for `e` gives
   `∑ q : Q, B.ρ q x = ∑ i : Fin n, B.ρ (g ^ i.1) x`.
4. `simpa [Rep.norm, Representation.norm]` identifies `B.norm.hom x` with
   `∑ q : Q, B.ρ q x` and closes the goal.

This is the source proof of lines 220–253 (docstring 218–219) verbatim after
the leading `unfold`.

## Dependencies

Imports: `Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic` (for
`orderOf_eq_card_of_forall_mem_zpowers` and `IsCyclic.image_range_orderOf`)
and the published target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`.
Other Mathlib facts used are `pow_eq_pow_iff_modEq`,
`Nat.ModEq.eq_of_lt_of_lt`, `Equiv.ofBijective`, `Equiv.sum_comp`,
`Finset.mem_image`, `Finset.mem_range` and the definitions `Rep.norm` and
`Representation.norm`. No other NYLL theorem is used.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 220–253 (docstring lines 218–219); ambient context lines 18–30; original file SHA-256
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
the source import closure is replaced by the published target module and the Mathlib module providing the cyclic-group lemmas (in the source they arrive transitively).
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
