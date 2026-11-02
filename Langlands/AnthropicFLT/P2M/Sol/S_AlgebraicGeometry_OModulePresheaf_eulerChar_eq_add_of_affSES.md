# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES`. Statement. `AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES`: over a field `k` and a separated
`π : V ⟶ Spec k`, for a short exact sequence `0 → F₁ → F₂ → F₃ → 0` on affine opens and an ordered
affine cover `K` for which all three have finite-dimensional Čech cohomology, the Euler
characteristics satisfy `χ(F₂) = χ(F₁) + χ(F₃)`.

Proof (namespace `P2mEulerAdd`). `cx F K`: the Čech complex as a cochain complex of `k`-modules;
`cxMap`: the induced maps of complexes; on cochains the sequence is short exact
(`cochainMap_injective`, `cochainMap_surjective`, `cochainMap_exact`; intersections are affine), giving
a short exact sequence of complexes `T S K` (`T_shortExact`). Section `Ident`: the homology of `cx F K`
is the FLT Čech cohomology (`nonempty_equiv_H0`, `nonempty_equiv_HSucc`, `finrank_homology_eq`),
finite-dimensional under the hypotheses, and zero beyond the number of cover members
(`subsingleton_homology_card_succ`). The long exact homology sequence (Mathlib) with
`injective_homologyMap_zero` gives the additivity of alternating sums of dimensions (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cx_d_hom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cx_d_zero_zero_hom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cxMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cxMap_f_hom`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.proj_inc_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cochainMap_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cochainMap_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.cochainMap_exact`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.T`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.T_shortExact`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.quotEquiv_aux`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.quotEquiv_aux₀`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.nonempty_equiv_HSucc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.nonempty_equiv_H0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.finrank_homology_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.finite_homology`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.subsingleton_homology_card_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.injective_homologyMap_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.P2mEulerAdd.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le` (same contribution).
Other imports: `Mathlib`.
