# NYLL M017.006: `DegreeData.frobeniusRestriction_mul`

Worker 747, 16 November 2026. Restriction of Frobenius elements is multiplicative.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestriction_mulStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestriction_mul`. The theorem's conclusion is that exact target applied to all of
its parameters; the source section variable
`{G : Type*} [Group G] [TopologicalSpace G]`, the explicit and implicit
parameters and the instance binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` are unchanged. The
target's Lean/Markdown pair and its imports are unchanged.

## Statement

For `D`, `K`, `L`, `hLK` as in the target and
`σ τ : D.FrobeniusElements K L hLK`, the theorem proves
`D.frobeniusRestriction K L hLK (σ * τ) =
D.frobeniusRestriction K L hLK σ * D.frobeniusRestriction K L hLK τ`, where
the product of Frobenius elements is the published instance M015.002
`frobeniusElementsMul`.

## Proof

After unfolding the target, `change` exposes the goal as
`D.extensionRestriction K.field L hLK (σ.1 * τ.1) =
D.extensionRestriction K.field L hLK σ.1 * D.extensionRestriction K.field L hLK τ.1`.
This is definitional: `frobeniusRestriction` applies `extensionRestriction`
to the underlying class, and the underlying class of `σ * τ` is `σ.1 * τ.1`
by the published definition `frobeniusMul`. The goal is then `map_mul` for
the monoid homomorphism `D.extensionRestriction K.field L hLK`.

This is the source proof of lines 217–228 (docstring 212–215) after the
leading `unfold`. The source `@[simp]` attribute (line 216) is omitted: the
theorem's stated type is the Statement proposition rather than a syntactic
equation, so the attribute would not provide the source rewrite rule.

## Dependencies

The only import is the published target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements`, which
supplies `frobeniusRestriction`, `extensionRestriction`, `FrobeniusElements`
and the instance `frobeniusElementsMul`. Mathlib fact: `map_mul`.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`, lines 217–228 (docstring lines 212–215, attribute line 216); ambient context lines 19–29; original file SHA-256
`75b2b32aeb8d07b1534b1ceb6c60052c71544a6029e1bc519c88905d9f63495f`. Its readable retained copy is under
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
the source import closure is replaced by the published target module, and the source `@[simp]` attribute is omitted as explained above.
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
