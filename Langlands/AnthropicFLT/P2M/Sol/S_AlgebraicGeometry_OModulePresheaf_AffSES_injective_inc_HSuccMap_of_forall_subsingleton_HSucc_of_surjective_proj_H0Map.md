# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map`. Statement. `AlgebraicGeometry.OModulePresheaf.AffSES.injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map`:
for a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of FLT presheaves of modules on affine opens
(`AffSES`) over a separated base, an ordered affine cover `K`, if all higher Čech groups of `F₃`
vanish and `H⁰(F₂) → H⁰(F₃)` is surjective, then `Hⁱ⁺¹(F₁) → Hⁱ⁺¹(F₂)` is injective for all `i`.

Proof (namespace `RM3SOL`), a diagram chase in the long exact sequence. On cochains the inclusion is
injective (`cochainMap_inc_injective`) and the sequence is exact (`cochainMap_proj_inc`,
`exists_cochainMap_inc_eq`). For degree `i + 1`, a class of `F₁` dying in `F₂` is `d g`; the image of
`g` in `F₃` is a cocycle, hence a coboundary by vanishing of `Hⁱ⁺¹(F₃)`; correcting `g` puts it in the
image of `F₁` (`injective_HSuccMap_succ`). In degree `1` the same argument uses surjectivity on `H⁰`
(`injective_HSuccMap_zero`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.RM3SOL.injective_HSuccMap_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.RM3SOL.cochainMap_inc_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.RM3SOL.cochainMap_proj_inc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.RM3SOL.exists_cochainMap_inc_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.RM3SOL.injective_HSuccMap_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_injective_inc_HSuccMap_of_forall_subsingleton_HSucc_of_surjective_proj_H0Map.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom` (Library).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `Mathlib.RingTheory.Noetherian.Basic`.
