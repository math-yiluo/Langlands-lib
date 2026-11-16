# NYLL M043.012: `rep_action_pow_fixed`

Worker 747, 16 November 2026. Every nonnegative power of a group element fixes a vector fixed by that element.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.rep_action_pow_fixedStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.rep_action_pow_fixed`. The theorem's conclusion is that exact target applied to all of
its parameters, with the source binders, binder kinds and implicit group
argument unchanged. The target's Lean/Markdown pair and its imports are
unchanged.

## Statement

For a group `R : IntegralRepGroupType`, a representation `B : Rep ℤ R`,
`g : R`, `x : B.V` with `hx : B.ρ g x = x` and `n : ℕ`, the theorem proves
`B.ρ (g ^ n) x = x`.

## Proof

After unfolding the target, the proof rewrites `B.ρ (g ^ n) x` to
`((B.ρ g)^[n]) x` with the file's private lemma
`rep_action_pow_eq_iterate_local`, and closes the goal with Mathlib's
`Function.IsFixedPt.iterate hx n`: a fixed point of a map is a fixed point of
each of its iterates.

The private lemma `rep_action_pow_eq_iterate_local` has exactly the
proposition of M043.010 and the proof of the M043.010 source (lines 257–261):
fix the instance `Module ℤ B.V := B.hV2` and rewrite with `map_pow` and
`Module.End.coe_pow`. The published M043.010 theorem
`Langlands.NYLL.ClassFormation.rep_action_pow_eq_iterate` was not yet in the
Library at this workspace base, so the argument is kept local under a private,
non-conflicting name; no second public copy is introduced.

This is the source proof of lines 279–283 (docstring 277–278) after the
leading `unfold`, with the source rewrite by `rep_action_pow_eq_iterate`
replaced by the local lemma.

## Dependencies

The only import is the published target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`.
Mathlib facts used: `map_pow`, `Module.End.coe_pow` and
`Function.IsFixedPt.iterate`.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 279–283 (docstring lines 277–278), with M043.010 at lines 257–261; ambient context lines 18–30; original file SHA-256
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
the source import closure is replaced by the published target module, and the unpublished prerequisite M043.010 is reproduced as the private lemma described above.
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
