# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit`. Statement. `AlgebraicGeometry.OModulePresheaf.isCoherent_isQuasicoherent_supportedIn_pushforwardUnit`: for a closed
immersion `ι : Z ⟶ V` and `π : V ⟶ Spec R`, the FLT presheaf `ι_* 𝒪_Z` (`pushforwardUnit π ι`) is
coherent, quasi-coherent, and supported in the image of `ι`.

Proof (namespace `P2mPushUnit`). Support: over opens disjoint from the image the preimage is empty, so
the sections vanish (`preimage_eq_bot`, `subsingleton_sections_of_eq_bot`, `supportedIn`). Coherence:
over an affine open `U` the map `Γ(V, U) → Γ(Z, ι⁻¹ U)` is surjective (`actHom_surjective`), so the
sections are a cyclic, finitely generated module (`isCoherent`). Quasi-coherence: `ι⁻¹ D(f)` is the
basic open of the image of `f` in the affine `ι⁻¹ U` (`preimage_basicOpen_eq`), whose sections are the
localization (`loc_core`, `smul_basicOpen`, `res_eq`, `isQuasicoherent`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.preimage_eq_bot`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.subsingleton_sections_of_eq_bot`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.image`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.coe_image`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.supportedIn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.res_rfl`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.appLE_rfl_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.actHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.actHom_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.isCoherent`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.loc_core`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.preimage_basicOpen_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.pre_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.smul_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.res_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.isQuasicoherent`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.P2mPushUnit.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library).
Other imports: `Mathlib`.
