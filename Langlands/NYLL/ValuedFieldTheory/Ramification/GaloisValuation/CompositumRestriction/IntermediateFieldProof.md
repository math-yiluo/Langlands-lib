# Joint restriction from an intermediate compositum

The theorem
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq`
proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldRestrictNormalHom_prod_injective_of_sup_eqStatement`.
Its type is exactly that closed proposition at independent universe parameters
`u, w`.

Unfolding the target gives, in order: explicit `K : Type u`, `[Field K]`,
implicit `Omega : Type w`, `[Field Omega]`, `[Algebra K Omega]`, explicit
`E₁ E₂ F : IntermediateField K Omega`, explicit `hE₁ : E₁ ≤ F` and
`hE₂ : E₂ ≤ F`, instances `[Normal K E₁]` and `[Normal K E₂]`, and explicit
`hsup : E₁ ⊔ E₂ = F`. The conclusion is injectivity of the product of the
published homomorphisms
`Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom Eᵢ F hEᵢ`,
each with type `(F ≃ₐ[K] F) →* (Eᵢ ≃ₐ[K] Eᵢ)`. Thus an automorphism of
the generated intermediate field is determined by these two restrictions.
The proof uses the target's existing objects and hypotheses; there are no
finiteness, separability, normality-of-`F`, valuation or local-field assumptions.

## Implemented proof

Given `σ τ : F ≃ₐ[K] F` with equal pairs of restrictions:

1. Form `Q : IntermediateField K F` from
   `RingHom.eqLocusField σ.toRingHom τ.toRingHom`. Its carrier consists of
   the elements on which `σ` and `τ` agree. Both automorphisms commute with
   `algebraMap K F`, so this subfield contains the image of `K`.
2. The local argument `hQ` treats either normal intermediate field `E ≤ F`.
   For `x` in `IntermediateField.restrict hEF`, membership supplies an element
   `y : E` whose image under `IntermediateField.inclusion hEF` is `x`.
   Evaluate the equality of restrictions at `y`, then apply `E.val`.
   The published M259.002 theorem
   `Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom_apply_val`
   rewrites this as `F.val (σ x) = F.val (τ x)`. Injectivity of `F.val`
   proves `x ∈ Q`.
3. Inside `F`, the two restricted fields have supremum top. Apply
   `IntermediateField.lift_injective F`; then `lift_sup`, `lift_restrict`,
   `lift_top` and `hsup` identify both lifted sides with `F`.
4. Project the given equality of pairs with `Prod.fst` and `Prod.snd`.
   The two applications of `hQ`, combined by `sup_le`, show `⊤ ≤ Q`.
   Every `x : F` therefore satisfies `σ x = τ x`, and `AlgEquiv.ext`
   proves equality of the automorphisms.

The construction of `Q` and `hQ` is local to the proof. This module introduces
only the named theorem as a public declaration.

## Source correspondence and modifications

Original source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean`,
SHA-256 `49dbe156918022358d4a244d2de1b16d00e4c6b0a43249bfd6ac6f77ef35318c`.
The [retained source](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean>)
was read in full. M331.002 has its docstring at lines 56–58, statement at
59–69 and proof at 70–147.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq` (M331.002) | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq` |

The source is already registered as
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The public inventory is
[`notes/reuse/nyll-public-port/m313-m336.md`, M331](../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m331).
No patch10 modification applies to this source module, and no applicable
NYLL erratum was found in the current Library's `notes/errata/`.

The original proof first restricts the two fields inside `F`, transports their
normality with `Normal.of_algEquiv`, proves their supremum is top using the
same lift calculation as step 3, and invokes source M331.001,
`restrictNormalHom_prod_injective_of_sup_eq_top`. It then compares the two
ordinary restrictions separately using the M259.002 evaluation formula.

This implementation replaces that M331.001 invocation with Mathlib's equalizer
construction. `RingHom.eqLocusField` is defined in
`Mathlib/Algebra/Field/Subfield/Basic.lean`, lines 475–483 in pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; its carrier is exactly the equality
locus and its field closure is already proved there. The two source evaluation
arguments are combined in `hQ`. Ordinary restrictions inside `F` and the
associated normality transports are consequently unnecessary.

Worker 305 supplied this equalizer route in a private exact-universe example,
checked in diagnostic `22ab5ba7-52e8-4e44-ab0b-d5abe23ce376`. Worker 224
adapted that example to this named theorem and wrote this documentation.
That focused dependency check justifies the smaller import set: the only
direct imports here are the published `CompositumRestriction.Statements`
target module and `IntermediateFieldRestriction.Proofs` for M259.002, both
under `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation`.
Mathlib's equalizer and intermediate-field interfaces arrive through these
imports. M331.001 is not a proof dependency of this implementation.

The complete source modifications are:

- Preserve the original copyright, license and author header verbatim; add a
  dated modification notice crediting Worker 224 and Worker 305.
- Isolate M331.002 in `CompositumRestriction.IntermediateFieldProof`, leaving
  M331.001 and M331.003 to their separate proof tasks.
- Prefix the namespace and `RamificationTheory` opening with `Langlands.NYLL`;
  omit the redundant opening of the enclosing namespace.
- Replace the original imports by the two published modules listed above.
- State the theorem as the exact closed published target at `.{u, w}` and
  introduce its unchanged telescope in the proof. Retain the original
  theorem basename and declaration docstring. Use `Ω` as the local name for
  `Omega`; omit the unused original section universe `v` and variable `P`.
- Replace the proof body by the equalizer route described above, retaining
  the source's lifted-supremum calculation and published evaluation formula.
- Omit the source's unnecessary `noncomputable section`; replace the module
  documentation with a description of this focused proof.

The target module, its Markdown, its dependencies, and the supplied
restriction maps are unchanged.

## Environment and attribution

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream targeted Lean 4.35.0-rc2 with Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Development compilation and theorem inspection succeeded with zero errors
and zero warnings in `lean_check` diagnostic
`ee8e54a4-d0ad-45cc-b54e-1dc62495a915`. Inspection reports the independent
level parameters `u, w` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development result is separate
from independent semantic review and staged exact-target validation.

Original author: Naganori Yamaguchi (assisted by OpenAI Codex), copyright 2026,
Apache-2.0. The original header is retained unchanged. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged;
their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
