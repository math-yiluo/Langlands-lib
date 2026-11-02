# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one`. Statement. `GoodReductionJacobian.AbelianSchemePropertyBundle.schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one`:
let `A`, `B` over `Spec R` have the abelian-scheme property bundle with group laws `L`, `M`. A morphism
`φ : A ⟶ B` over `R` that sends the unit to the unit is a homomorphism: `φ(x · y) = φ(x) · φ(y)` for all points
`x, y`.

Proof. Consider the defect `δ(x, y) = φ(xy) (φ(x) φ(y))⁻¹`, a morphism `A ×_R A ⟶ B` (`defect`); it suffices to show
that `δ` is the unit (`comp_defect_eq_one`). On each fibre over a point `s` of `Spec R`, the fibres are abelian
varieties over `κ(s)` and `φ_s` is a homomorphism by the ported
`RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle` (`nmComp_mul_of_fibre`).
`A ×_R A` is proper and flat with geometrically reduced and connected fibres (`geometricallyReduced`,
`geometricallyConnected`), so global functions on it come from the base (ported
`bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`), and the ported
`comp_section_comp_eq_of_isClosedMap_of_surjective_app` shows that `δ` factors through `Spec R` and equals its value on
the unit section, which is the unit.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.inv_natural`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.comp_nmComp`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.nmComp_one`
- abbrev `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.tP`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.X₁`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.X₂`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.defect`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.comp_defect`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.comp_defect_eq_one`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.one_coe`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.subsingleton_spec_field`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.connectedSpace_of_bundle`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.nmComp_mul_of_fibre`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.geometricallyReduced`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.geometricallyConnected`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.H2bHomExt.main`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension` (Library), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange` (Library), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app` (same contribution).
Other imports: `Mathlib`.
