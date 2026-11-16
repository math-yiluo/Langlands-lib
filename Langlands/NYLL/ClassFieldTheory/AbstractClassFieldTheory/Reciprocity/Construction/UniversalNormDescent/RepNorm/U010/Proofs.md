# NYLL M043.010: `rep_action_pow_eq_iterate`

Worker 747, 16 November 2026. Powers of a group element act on a representation as iterates of its action map.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.rep_action_pow_eq_iterateStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.rep_action_pow_eq_iterate`. The theorem's conclusion is that exact target applied to all of
its parameters, with the source binders, binder kinds and implicit group
argument unchanged. The target's Lean/Markdown pair and its imports are
unchanged.

## Statement

For a group `R : IntegralRepGroupType`, a representation `B : Rep ℤ R`,
`g : R`, `n : ℕ` and `x : B.V`, the theorem proves
`B.ρ (g ^ n) x = ((B.ρ g)^[n]) x`.

## Proof

After unfolding the target, the proof fixes the local instance
`Module ℤ B.V := B.hV2`, the module structure carried by `B`, through which
`B.ρ` is a monoid homomorphism into `Module.End ℤ B.V`. Without it (checked
in development), elaborating the rewrite synthesizes the canonical structure
`AddCommGroup.toIntModule` on `B.V`, which Lean reports as not definitionally
equal to `B.hV2`, and the proof fails. Then `map_pow` rewrites `B.ρ (g ^ n)` to `(B.ρ g) ^ n`
and Mathlib's `Module.End.coe_pow` identifies the coercion of the `n`-th
power of an endomorphism with the `n`-fold iterate of its coercion, which
closes the goal.

This is the source proof of lines 257–261 (docstring 255–256) verbatim after
the leading `unfold`.

## Dependencies

The only import is the published target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements`.
The proof uses Mathlib's `map_pow` and `Module.End.coe_pow` (available
through that module's `Mathlib.RepresentationTheory.Rep.Basic` import). It
uses no other NYLL theorem.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 257–261 (docstring lines 255–256); ambient context lines 18–30; original file SHA-256
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
the source import closure is replaced by the published target module.
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
