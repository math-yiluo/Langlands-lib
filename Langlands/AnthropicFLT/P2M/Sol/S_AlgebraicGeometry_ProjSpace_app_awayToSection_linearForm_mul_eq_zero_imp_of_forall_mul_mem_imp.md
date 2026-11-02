# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 20 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (5 places), `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp`. Statement. `AlgebraicGeometry.ProjSpace.app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp`: let
`ιk : Z_k ⟶ ℙⁿ_k` be a closed immersion over a field and `J` an ideal whose forms of degree `≥ m` are
exactly those vanishing on `Z_k`. If the linear form `ℓ = ∑ aⱼ Xⱼ` is a non-zero-divisor on `J` in
degrees `≥ m` (`ℓ f ∈ J` implies `f ∈ J`), then on every chart `ιk⁻¹ D₊(Xᵢ)` multiplication by the
dehomogenized form `ℓ / Xᵢ` is injective on sections.

Proof. `awayMk` writes dehomogenized forms (`val_awayMk`, multiplicativity `awayMk_mul`,
`awayMk_X_pow_mul`). A section `t` of the chart is the image of `F / Xᵢ^d` for a form `F`; by the ported
`ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal` (applied to the kernel
ideal of `ιk`), after multiplying by a power of `Xᵢ` the relation `(ℓ / Xᵢ) t = 0` says that
`ℓ · Xᵢ^N F` vanishes on `Z_k`, hence lies in `J`; the hypothesis gives `Xᵢ^N F ∈ J`, so `t = 0`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.awayMk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.val_awayMk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.awayMk_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.awayMk_X_pow_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_app_awayToSection_linearForm_mul_eq_zero_imp_of_forall_mul_mem_imp.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal` (same contribution).
Other imports: `Mathlib`.
