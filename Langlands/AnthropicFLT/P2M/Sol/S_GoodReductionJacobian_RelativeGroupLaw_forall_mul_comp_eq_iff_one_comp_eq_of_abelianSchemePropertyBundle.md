# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 20 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (4 places), `Scheme.{0}` → `Scheme.{uz}` (4 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle`. Statement. `GoodReductionJacobian.RelativeGroupLaw.forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle`: for
commutative group schemes `A`, `B` over `Spec S` with the abelian-scheme property bundle and a morphism
`φ : A ×_S Spec S' ⟶ B` over `S`, `φ` is a homomorphism (on all points over `Spec S'`) iff it sends the unit section
to the unit.

Proof. A homomorphism preserves units (local `lift_one_eq`, from `φ(1·1) = φ(1)φ(1)`). Conversely, the base changes
of `A` and `B` to `Spec S'` have the property bundle (ported `AbelianSchemePropertyBundle.of_isPullback`), and the
ported `AbelianSchemePropertyBundle.schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one` applies to `φ`
viewed as a morphism over `S'`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle.K63H4a.lift_one_eq`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange` (Library), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one` (same contribution).
Other imports: none.
