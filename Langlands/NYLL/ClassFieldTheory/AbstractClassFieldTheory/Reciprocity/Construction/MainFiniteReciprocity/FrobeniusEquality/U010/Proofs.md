# NYLL M065.010: `DegreeData.frobenius_eq_of_restriction_eq_of_exponent_eq`

Worker 747, 16 November 2026. Frobenius lifts with equal restriction and equal
Frobenius exponent are equal.

This file proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobenius_eq_of_restriction_eq_of_exponent_eqStatement` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity.FrobeniusEquality.Statements`) with the required theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobenius_eq_of_restriction_eq_of_exponent_eq`. The theorem's conclusion is that exact target applied to all of
its parameters; the source universe `u`, the section variable
`{G : Type u} [Group G] [TopologicalSpace G]`, the explicit and implicit
parameters and the instance binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` are unchanged. The
target's Lean/Markdown pair and its imports are unchanged.

## Statement

For `D : DegreeData G`, `K : FiniteResidueAbstractField D`, a closed subgroup
`L` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` and normal extension
subgroup, and Frobenius elements `σ τ : D.FrobeniusElements K L hLK` with
`hRestriction : D.frobeniusRestriction K L hLK σ = D.frobeniusRestriction K L hLK τ`
and `hExponent : D.frobeniusExponent K L hLK σ = D.frobeniusExponent K L hLK τ`,
the theorem proves `σ = τ`.

## Proof

After unfolding the target, the file's private lemma
`frobenius_eq_of_restriction_eq_of_degree_eq_local` applied to `hRestriction`
reduces the goal to
`D.extensionNormalizedDegree K L hLK σ.1 = D.extensionNormalizedDegree K L hLK τ.1`.
Rewriting both sides with the private lemma
`extensionNormalizedDegree_frobenius_eq_pow_local` turns them into
`Multiplicative.ofAdd (1 : ZHat) ^ D.frobeniusExponent K L hLK σ` and the same
power with `τ`, and rewriting with `hExponent` closes the goal.

The three private lemmas reproduce unpublished prerequisites with exactly
their propositions:

- `extensionNormalizedDegree_frobenius_eq_pow_local` is M014.014
  `extensionNormalizedDegree_frobenius_eq_pow` (the proposition of the
  published target
  `Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_eq_powStatement`,
  stated unfolded). As in the source (`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`,
  lines 319–326, SHA-256
  `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`), it is
  `(Exists.choose_spec σ.2).2`: the published `frobeniusExponent` is
  `Exists.choose σ.2`, where `σ.2` is the membership proof
  `∃ n, 0 < n ∧ D.extensionNormalizedDegree K L hLK σ.1 = Multiplicative.ofAdd 1 ^ n`
  of the published `FrobeniusElements` subtype.
- `extensionRestriction_normalizedDegree_joint_injective_local` is M017.005:
  for classes of `a b : K.field.toSubgroup` with equal restriction and equal
  normalized degree, `QuotientGroup.eq` gives
  `a⁻¹ * b ∈ extensionSubgroup K.field L hLK`; the published M011.010
  `normalizedDegree_ker`, stated unfolded as the local
  `have hker : (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field`,
  reduces inertia membership of `a⁻¹ * b` to
  `D.normalizedDegree K (a⁻¹ * b) = 1`, which follows from `map_mul`,
  `map_inv`, the degree equality and `inv_mul_cancel`; so `a⁻¹ * b` lies in
  `D.extensionInertiaWithin K.field L hLK` and the classes agree.
- `frobenius_eq_of_restriction_eq_of_degree_eq_local` is M017.007: by
  `Subtype.ext` and the local joint-injectivity lemma applied to
  `Prod.ext hRestriction hDegree`.

The published theorems
`Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_eq_pow`
(M014.014, routed to Task `0ca66bab-09fd-459e-a5fe-46b1867d3f08`),
`Langlands.NYLL.ClassFormation.DegreeData.extensionRestriction_normalizedDegree_joint_injective`
(M017.005) and
`Langlands.NYLL.ClassFormation.DegreeData.frobenius_eq_of_restriction_eq_of_degree_eq`
(M017.007) were not yet in the Library at this workspace base, so their
arguments are kept local under private, non-conflicting names; no second
public copy is introduced. The M017 arguments follow
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`
(SHA-256 `75b2b32aeb8d07b1534b1ceb6c60052c71544a6029e1bc519c88905d9f63495f`),
lines 185–210 and 232–248.

This is the source proof of lines 313–326 (docstring 311–312) after the
leading `unfold`, with the source references to M017.007 and M014.014
replaced by the local lemmas.

## Dependencies

Imports: the published proof module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs` (M011.010
`normalizedDegree_ker`) and the published target module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity.FrobeniusEquality.Statements`, which
supplies `frobeniusExponent`, `FrobeniusElements`, `frobeniusRestriction`,
`extensionRestriction`, `extensionNormalizedDegree`, `extensionInertiaWithin`
and `extensionSubgroup`. Mathlib facts: `Exists.choose_spec`,
`Quotient.inductionOn₂'`, `QuotientGroup.eq`, `Subtype.ext`, `Prod.ext`,
`map_mul`, `map_inv` and `inv_mul_cancel`.

## Source and attribution

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainFiniteReciprocity.lean`, lines 313–326 (docstring lines 311–312); ambient context lines 29–43 and the section `equalFrobeniusLifts`, lines 305–309; original file SHA-256
`aa0954d0883cd84c712e46b9bdd98456a21cad95119a37acc3164141fc539bad`. Its readable retained copy is under
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
the source import closure is replaced by the published target module and the published M011.010 proof module; the source opens of `KummerTheory`, `CategoryTheory` and `BigOperators` are not needed and omitted; and the unpublished prerequisites M014.014, M017.005 and M017.007 are reproduced as the private lemmas described above.
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
