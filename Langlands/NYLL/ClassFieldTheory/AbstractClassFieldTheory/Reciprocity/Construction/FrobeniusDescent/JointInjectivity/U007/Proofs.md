# NYLL M017.007: `DegreeData.frobenius_eq_of_restriction_eq_of_degree_eq`

Worker 747, 16 November 2026. Frobenius elements with equal restriction and equal normalized degree are equal.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobenius_eq_of_restriction_eq_of_degree_eqStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobenius_eq_of_restriction_eq_of_degree_eq`. The theorem's conclusion is that exact target applied to all of
its parameters; the source section variable
`{G : Type*} [Group G] [TopologicalSpace G]`, the explicit and implicit
parameters and the instance binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` are unchanged. The
target's Lean/Markdown pair and its imports are unchanged.

## Statement

For `D`, `K`, `L`, `hLK` as in the target, Frobenius elements
`σ τ : D.FrobeniusElements K L hLK` with
`hRestriction : D.frobeniusRestriction K L hLK σ = D.frobeniusRestriction K L hLK τ`
and
`hDegree : D.extensionNormalizedDegree K L hLK σ.1 = D.extensionNormalizedDegree K L hLK τ.1`,
the theorem proves `σ = τ`.

## Proof

After unfolding the target, `Subtype.ext` reduces `σ = τ` to equality of the
underlying classes `σ.1 = τ.1`. The file's private lemma
`extensionRestriction_normalizedDegree_joint_injective_local` (injectivity of
the joint restriction/degree map) reduces this to equality of the pairs, which
is `Prod.ext hRestriction hDegree` (the restriction of `σ` is by definition
the restriction of `σ.1`).

The private lemma has exactly the proposition of M017.005 and reproduces the
proof described for M017.005 (source lines 185–210):

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

The published M017.005 theorem
`Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_normalizedDegree_joint_injective`
was not yet in the Library at this workspace base, so its argument is kept
local under a private, non-conflicting name; no second public copy is
introduced.

This is the source proof of lines 232–248 (docstring 230–231) after the
leading `unfold`, with the source reference to M017.005 replaced by the local
lemma.

## Dependencies

Imports: the published proof module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs` (M011.010
`normalizedDegree_ker`, used by the local lemma) and the published target
module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent.JointInjectivity.Statements`. Mathlib facts: `Subtype.ext`, `Prod.ext` and
those listed for the local lemma.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`, lines 232–248 (docstring lines 230–231), with M017.005 at lines 185–210; ambient context lines 19–29; original file SHA-256
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
the source import closure is replaced by the published target module and the published M011.010 proof module, and the unpublished prerequisite M017.005 is reproduced as the private lemma described above.
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
