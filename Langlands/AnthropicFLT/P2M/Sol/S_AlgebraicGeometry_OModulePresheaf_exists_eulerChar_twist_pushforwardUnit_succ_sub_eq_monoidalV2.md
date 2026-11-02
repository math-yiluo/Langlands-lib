# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2`. Statement. `AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2`:
let `π : V ⟶ Spec k` be proper over a field, `K` an ordered affine cover, `L` a locally trivial
module on `V`, and `Z₀ ⊆ V` a nonempty closed subset whose reduced subscheme `Z` is integral. Then
there are closed subsets `Y₁, Y₂ ⊊ Z₀` and coherent, quasi-coherent FLT presheaves `G₁`, `G₂`
supported in `Y₁`, `Y₂`, such that for all `n`,
`χ(𝒪_Z ⊗ L^{n+1}) - χ(𝒪_Z ⊗ L^n) = χ(G₁ ⊗ L^{n+1}) - χ(G₂ ⊗ L^n)` (Euler characteristics of twists of
the pushforward of `𝒪_Z`, for the cover `K`).

Proof (namespace `P2mTwistStep`). Section `General`: tensor powers of `L` are locally trivial and have
flat sections, twists of coherent quasi-coherent presheaves stay coherent and quasi-coherent with
finite Čech cohomology for proper `π`, Euler characteristics are additive on short exact sequences
after twisting (`eulerChar_twist_add`, from the ported tensor-exactness and additivity results) and
invariant under isomorphisms on affine opens (`eulerChar_eq_of_bijective`). Section `Setup`: for an
ideal sheaf `I` on `Z`, the sequence `0 → K_I → 𝒪_Z → 𝒪_{Z_I} → 0` (`rho`, `sesI`), with `K_I(U) ≅ I(U)`
(`kappa`), all coherent and quasi-coherent (`OZ_good`, `OZI_good`, `KI_good`); for `I ≠ ⊥` on the
integral `Z`, the support `YI` of `𝒪_{Z_I}` is strictly smaller than `Z₀` (`YI_lt`). Section `Theta`:
given ideal sheaves `I`, `J` and an isomorphism `e : I ⊗ L|_Z ≅ J` on affine opens (a local
trivialization of `L` on `Z` used to compare `I` with a twist of `J`), the twists satisfy
`K_I ⊗ L^{n+1} ≅ K_J ⊗ L^n` on affine opens (`Theta`, `ThetaHom`, `ThetaHom_bijective`). Section
`Main`: choosing `I`, `J` from a nonzero section of `L` over an affine open of `Z` (both nonzero),
additivity gives the stated identity with `G₁ = 𝒪_{Z_I}` and `G₂ = 𝒪_{Z_J}`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.locTriv_tensorPow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.coh_twist`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.cechFinite_twist`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.flat_sections`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.eulerChar_twist_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.eulerChar_eq_of_bijective`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.ZZ`
- private abbrev `P2mTwistStep.ι`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.OZ`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.ιI`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.OZI`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.W`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.W_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.res_rfl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.appLE_rfl_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.appLE_comp_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.rho`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.rho_app`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.KI`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.sesI`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.mem_KI_iff`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.algVZ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.kappa`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.kappa_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.kappa_symm_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.KI_res_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.OZ_good`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.OZI_good`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.KI_good`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.YI`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.range_ι`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.YI_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.YI_lt`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.exists_affine_nonempty`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.ne_bot_of_ideal_ne_bot`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.M`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.eta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.map_eta`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.tau`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.tau_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.map_tau_tmul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.twistIso`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.twistIso_tmul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.Theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.Theta_tmul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.ThetaHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.ThetaHom_bijective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.P2mTwistStep.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin_monoidalV2` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ker` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ker` (same contribution).
Other imports: `Mathlib`.
