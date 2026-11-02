# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 16 here); in 2 lines the replacements `Type` (universe 0) → `Type uz` (2 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal`. Statement. `AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal`: for an
ideal sheaf `𝓘` on `ℙⁿ_A`, if `H / Xᵢ^a` lies in the ideal of `𝓘` on the chart `D₊(Xᵢ)` (with `H` a form
of degree `a`), then for every `N₀` there is `N ≥ N₀` such that `Xᵢ^N H / Xⱼ^{N + a}` lies in the ideal
of `𝓘` on every chart `D₊(Xⱼ)`.

Proof (namespace `SatVanishAux`). On `D₊(Xⱼ)`, the element `elt i j a H N = Xᵢ^N H / Xⱼ^{N + a}` equals
`(Xᵢ/Xⱼ)^{N + a} · (H / Xᵢ^a)` on the overlap (`ratio_pow_mul_elt`); the overlap is the basic open of
`Xᵢ/Xⱼ` in the chart (`isLocalizationElem_eq_ratio`). Since ideal sheaves are quasi-coherent, the
membership of `H / Xᵢ^a` on `D₊(Xᵢ)` restricted to the overlap means that a power of `Xᵢ/Xⱼ` times
`elt` lies in the ideal on `D₊(Xⱼ)` (`claim`); take `N` large enough for all `j`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.elt`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.val_elt`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.val_ratio_pow`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.ratio_pow_mul_elt`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.isLocalizationElem_eq_ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.SatVanishAux.claim`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution).
Other imports: `Mathlib`.
