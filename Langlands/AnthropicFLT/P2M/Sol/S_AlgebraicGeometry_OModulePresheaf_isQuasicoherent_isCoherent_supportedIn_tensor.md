# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor`. Statement. `AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor`: the tensor product
`F ⊗ G` of FLT presheaves of modules is quasi-coherent if `F` and `G` are, coherent if `F` and `G`
are, and supported in `Y` if `F` or `G` is.

Proof (namespace `P2mTensorStableSol`). Section `Alg`: if `M → M'` and `N → N'` are localizations at
`S`, then `M ⊗_A N → M' ⊗_{A'} N'` is a localization at `S` (`diag`, `isLocalizedModule_diag`).
Section `Datum`: quasi-coherence is equivalent to the restrictions to basic opens being localizations
(`resBO`, `isLocalizedModule_resBO`, `qcAt_of_isLocalizedModule`). Section `Card`: hence the tensor
product is quasi-coherent; tensor products of finitely generated modules are finitely generated
(coherence); and the sections of `F ⊗ G` vanish where those of `F` or of `G` vanish (support).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.diag`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.diag_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.isLocalizedModule_diag`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.modBO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.isScalarTower_modBO`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.resBO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.resBO_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.isLocalizedModule_resBO`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.qcAt_of_isLocalizedModule`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.isQuasicoherent_tensor`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.isCoherent_tensor`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.supportedIn_tensor`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.P2mTensorStableSol.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (same contribution).
Other imports: `Mathlib`.
