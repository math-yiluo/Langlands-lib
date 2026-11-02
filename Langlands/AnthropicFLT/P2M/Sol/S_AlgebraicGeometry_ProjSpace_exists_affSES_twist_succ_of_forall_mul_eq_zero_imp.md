# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 24 here); in 4 lines the replacements `Type` (universe 0) → `Type uz` (1 place), `Scheme.{0}` → `Scheme.{uz}` (3 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp`. Statement. `AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp` (hyperplane sequence):
let `ιk : Z_k ⟶ ℙⁿ_k` be a closed immersion, `ℓ` a linear form whose dehomogenizations are
non-zero-divisors on the charts of `Z_k`, `𝓘ℓ` the ideal sheaf of `ℓ`, and `ι' : Z' ⟶ ℙⁿ_k` the closed
subscheme with ideal `ker ιk ⊔ 𝓘ℓ` (the hyperplane section). For every `d` there are an FLT presheaf
`F₃` on `Z_k`, a short exact sequence `0 → 𝒪_{Z_k}(d) → 𝒪_{Z_k}(d + 1) → F₃ → 0` on affine opens
(multiplication by `ℓ`), and isomorphisms of Čech cohomology between `F₃` and `𝒪_{Z'}(d + 1)` under
which the image in `H⁰` of a section given in the charts by a form `G` of degree `d + 1` is the section
of `𝒪_{Z'}(d + 1)` given by the same form.

Proof (namespace `P2mRM1Reduce`). The ported
`ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` gives the section `θ(ℓ)` of
`𝒪(1)` represented by `ℓ`; the ported `ProjSpace.exists_hom_twist_val_eq_mul_and_injective_of_cocycle`
gives the multiplication map `μ : 𝒪(d) → 𝒪(d + 1)` by it, injective on affine opens by the
non-zero-divisor hypothesis. Take `F₃ = coker μ`; the ported
`ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup` identifies the Čech cohomology of the
cokernel with that of `𝒪_{Z'}(d + 1)`, compatibly with sections given by forms
(`restrictFun_injective_of_le_le` handles restrictions between equal opens).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.P2mRM1Reduce.restrictFun_injective_of_le_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution).
Other imports: `Mathlib`.
