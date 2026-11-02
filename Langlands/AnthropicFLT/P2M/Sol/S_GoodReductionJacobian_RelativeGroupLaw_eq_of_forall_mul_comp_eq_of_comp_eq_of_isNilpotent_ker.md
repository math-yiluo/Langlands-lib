# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 19 here); in 25 lines the replacements `Type` (universe 0) → `Type uz` (15 places), `Scheme.{0}` → `Scheme.{uz}` (16 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker`. Statement. `GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker` (rigidity along
nilpotent thickenings): let `A`, `B` over `Spec S` be commutative group schemes with the abelian-scheme property
bundle, `ψ : S' → S''` surjective with nilpotent kernel and `φ₁, φ₂ : A ×_S Spec S' ⟶ B` homomorphisms over `S`. If
`φ₁` and `φ₂` agree on `A ×_S Spec S''`, then `φ₁ = φ₂`.

Proof. Section `Thickening`: let `δ = φ₁ φ₂⁻¹` and `ε` the unit (`δpt`, `εpt`); `φ₁ = φ₂` iff `δ = ε`
(`φ_eq_of_δ_eq_ε`), and `δ` agrees with `ε` after composing with the closed immersion
`A ×_S Spec S'' ⟶ A ×_S Spec S'`, which is a homeomorphism (`surjective_jmap`), so `δ` and `ε` agree on points
(`δ_base_eq`). Section `Local`: for a prime `𝔭` of `S'`, let `A_𝔭` be the base change to the localization `S'_𝔭`
(`Rp`, `Ap`). As `A_𝔭` is proper and flat over the local ring with `Γ(A_𝔭, 𝒪) = S'_𝔭` (`bijective_pp_appTop`, from
the ported `bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing` and
`AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback`), and `δ` maps `A_𝔭` into an affine
neighbourhood of the unit section (`base_mem_of_isOpen`), `δ` restricted to `A_𝔭` factors through the base and is
determined by its composite with the unit section, which is the unit (`σp_δ`, `cp_δ`). The localizations cover
`A ×_S Spec S'` jointly, so `δ = ε` (`δ_eq_ε`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.map_one_of_map_mul`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.map_inv_of_map_mul`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.inv_natural`
- structure `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.A'`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.p`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.tA`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.Φ₁`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.Φ₂`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.δpt`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.εpt`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.δ`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.ε`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.φ_eq_of_δ_eq_ε`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.comp_δ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.comp_ε`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.comp_δ_eq_comp_ε_of`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.ε_eq`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σ_p`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σ_φ₁`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σ_φ₂`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σ_δ`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.jmap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.jmap_fst`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.jmap_p`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.isPullback_jmap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.surjective_specMap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.surjective_jmap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.δ_base_eq`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.Rp`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.lam`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.Ap`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.cp`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.pp`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.mem_range_lam_iff`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.base_mem_of_isOpen`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.bijective_pp_appTop`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σp`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σp_cp`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σp_pp`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.σp_δ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.cp_δ`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.flat_lam`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.P2mWs30HomUnram.HData.δ_eq_ε`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback` (same contribution).
Other imports: none.
