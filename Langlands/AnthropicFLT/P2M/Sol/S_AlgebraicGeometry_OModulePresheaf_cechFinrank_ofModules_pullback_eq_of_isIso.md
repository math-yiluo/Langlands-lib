# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso`. Statement. `AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso`: let `Φ : P ⟶ P'` be an
isomorphism of schemes, `π' : P' ⟶ Spec R` separated and `N` an invertible module on `P'`. Then the
Čech dimensions (`cechFinrank`, for any ordered affine covers `𝔚` of `P` and `𝔚'` of `P'`) of
`Φ^* N` over `Φ ≫ π'` and of `N` over `π'` agree.

Proof (namespace `P2mAutInv`). `cechEquiv_of_affHom_inverse`: mutually inverse `AffHom`s induce
isomorphisms of Čech cohomology. Section `twistIso`: for the isomorphism `Φ`, the twist of the
pushforward of the structure sheaf by `N` is isomorphic on affine opens to `N` itself (`fwd`, `bwd`,
inverse by `bwd_fwd`, `fwd_bwd`), giving `cechEquiv_twist_pushforwardUnit_of_isIso`. Main proof: `Φ^* N`
is locally trivial, hence quasi-coherent (ported
`OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial`), so its Čech cohomology is independent
of the cover (ported `OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated`,
comparing `𝔚` with `𝔚'.comap Φ`); the ported
`OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit` compares the
pulled-back cover with the twisted pushforward; composing the three isomorphisms gives equal
dimensions in every degree.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.cechEquiv_of_affHom_inverse`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.eU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.eU_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.eU_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.eEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.pf_smul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.onePf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.eU_mul_onePf`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.fwd`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.fwd_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.fwd_smul_sections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.bwdBil`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.bwd`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.bwd_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.bwd_fwd`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.fwd_bwd`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.fwdHom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.bwdHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.P2mAutInv.cechEquiv_twist_pushforwardUnit_of_isIso`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` (Library).
Other imports: `Mathlib`.
