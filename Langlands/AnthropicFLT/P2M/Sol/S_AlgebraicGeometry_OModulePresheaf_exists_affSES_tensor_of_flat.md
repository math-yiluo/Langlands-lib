# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat`. Statement. `AlgebraicGeometry.OModulePresheaf.exists_affSES_tensor_of_flat`: if `G` is an FLT presheaf of modules
whose sections over each affine open `U` are flat over `Γ(V, U)`, then tensoring a short exact
sequence `0 → F₁ → F₂ → F₃ → 0` on affine opens with `G` gives a short exact sequence
`0 → F₁ ⊗ G → F₂ ⊗ G → F₃ ⊗ G → 0`, acting on pure tensors by `x ⊗ y ↦ (inc x) ⊗ y` and
`x ⊗ y ↦ (proj x) ⊗ y`.

Proof (namespace `P2mTensorExact`). `appT`, `rTensorAffHom`: a morphism on affine opens induces
`φ ⊗ id_G` on the tensor presheaves (natural in restriction, checked on pure tensors). The sequence
of sections is exact (`exact_appSections`); `rTensor` preserves surjectivity, and by flatness of
`G(U)` also injectivity and exactness (`Module.Flat.rTensor_preserves_injective_linearMap`,
`Module.Flat.rTensor_exact`), giving `affSES`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.appT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.appT_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.appT_tmul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.rTensorAffHom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.rTensorAffHom_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.exact_appSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.affSES`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.P2mTensorExact.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
