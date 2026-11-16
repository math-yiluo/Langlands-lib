# NYLL M017.005: `DegreeData.extensionRestriction_normalizedDegree_joint_injective`

Worker 747, 16 November 2026. Restriction to `G(L/K)` and normalized degree jointly distinguish elements of `G(\widetilde L/K)`.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_normalizedDegree_joint_injectiveStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_normalizedDegree_joint_injective`. The theorem's conclusion is that exact target applied to all of
its parameters; the source section variable
`{G : Type*} [Group G] [TopologicalSpace G]`, the explicit and implicit
parameters and the instance binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` are unchanged. The
target's Lean/Markdown pair and its imports are unchanged.

## Statement

For `D : DegreeData G`, `K : FiniteResidueAbstractField D`, a closed subgroup
`L` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` and normal extension
subgroup, the theorem proves that the map
`q ↦ (D.extensionRestriction K.field L hLK q, D.extensionNormalizedDegree K L hLK q)`
on `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` is injective.

## Proof

After unfolding the target:

Take `q r` in `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK`
with equal images; by `Quotient.inductionOn₂'` they are classes of
`a b : K.field.toSubgroup`, and by `QuotientGroup.eq` it suffices to show
`a⁻¹ * b ∈ D.extensionInertiaWithin K.field L hLK`, which by definition is
the intersection `L.toSubgroup.subgroupOf K.field.toSubgroup ⊓
D.fieldInertiaWithin K.field`.
- First components: the restrictions agree, i.e. the classes of `a` and
  `b` in `K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK` agree
  (`congrArg Prod.fst`); `QuotientGroup.eq` gives
  `a⁻¹ * b ∈ extensionSubgroup K.field L hLK`.
- Second components: `D.normalizedDegree K a = D.normalizedDegree K b`
  (`congrArg Prod.snd`; the factorized degree of a class is by definition
  the normalized degree of a representative). The published theorem
  `Langlands.NYLL.ClassFormation.DegreeData.normalizedDegree_ker` (M011.010)
  has type `normalizedDegree_kerStatement D K`; it is first stated
  unfolded as the local `have hker : (D.normalizedDegree K).toMonoidHom.ker
  = D.fieldInertiaWithin K.field`, and rewriting backwards with `hker`
  reduces the inertia membership to `D.normalizedDegree K (a⁻¹ * b) = 1`,
  which follows from `map_mul`, `map_inv`, the degree equality and
  `inv_mul_cancel`.

This is the source proof of lines 185–210 (docstring 183–184) after the
leading `unfold`; the only change is that the source rewrite
`rw [← D.normalizedDegree_ker K]` with the Statement-typed published theorem
is performed through the unfolded local `have hker`, as the task directs.

## Dependencies

Imports: the published proof module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs` (for M011.010
`normalizedDegree_ker`) and the published target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements`.
Published definitions used through the target module: `extensionRestriction`,
`extensionInertiaWithin`, `extensionNormalizedDegree`, `normalizedDegree`,
`fieldInertiaWithin` and `extensionSubgroup`. Mathlib facts:
`Quotient.inductionOn₂'`, `QuotientGroup.eq`, `map_mul`, `map_inv` and
`inv_mul_cancel`.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`, lines 185–210 (docstring lines 183–184); ambient context lines 19–29; original file SHA-256
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
the source import closure is replaced by the published target module and the published M011.010 proof module, and the Statement-typed rewrite is unfolded as described above.
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
