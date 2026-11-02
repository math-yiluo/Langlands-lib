# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 544, line 555 here): `(∑ v ∈ (f k).support, MvPolynomial.monomial v (MvPolynomial.coeff v (f k)))` is replaced by `(∑ v ∈ (f k).support, MvPolynomial.monomial v ((f k).coeff v))`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 546, line 557 here): `(MvPolynomial.monomial v (MvPolynomial.coeff v (f k))) := map_sum _ _ _` is replaced by `(MvPolynomial.monomial v ((f k).coeff v)) := map_sum _ _ _`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 573, line 584 here): `have hmon : MvPolynomial.monomial α (MvPolynomial.coeff α (f k))` is replaced by `have hmon : MvPolynomial.monomial α ((f k).coeff α)`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 574, line 585 here): `= MvPolynomial.coeff α (f k) • ProjSpaceCech.GradedModule.monMul (ProjSpaceCech.GradedModule.FD A n (σ.d₀ k))` is replaced by `= (f k).coeff α • ProjSpaceCech.GradedModule.monMul (ProjSpaceCech.GradedModule.FD A n (σ.d₀ k))`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion`. Statement. `AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion`:
for a closed immersion `ι : Z ⟶ ℙⁿ_A` over a noetherian ring there is `d₂` such that for every `d ≥ d₂`,
every element of degree `d` of the graded module `twistGradedModule ι` (compatible families of
sections of `𝒪_Z(d)` on the charts) is given in all charts by a form `F` of degree `d`.

Proof (namespace `PolySurjBody`). Sections `Frac` and `Comp`: dehomogenization of forms and its pullback
to the charts of `Z` (`pullAway`), with additivity, multiplicativity and restriction lemmas; the
transition functions are pulled-back ratios (`frameUnit_eq_pullAway`); sections of the charts are
`F / Xⱼ^e` up to powers of the frame units (`exists_eq_pullAway_mk`, `exists_pow_mul_eq_zero`).
Sections `Units`, `UnitsMon`: forms give elements `unitFam` of the graded module, compatible with
multiplication by the variables and monomials. Sections `Glob`, `Extract`, `HomLemmas`, `PowUnit`,
`Extract2`: global sections of the graded-module Čech complex and how they determine elements. Main
argument: the ported `ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule` embeds a finitely
generated graded module `D'` (the forms, generated by finitely many `unitFam`s) into the twist module
with saturated cokernel; by the ported `ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG`
and `ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated`, in large degrees every element is the
image of an element of `D'`, i.e. of a form (`absorb` handles the multiplication by powers of the
variables).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.map_appTop_π_eq_awayToSection_algebraMap`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.val_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.frac_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.frac_smul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.awayMap_frac_eq`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.restrictFun_pullAway_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.restrictFun_pullAway_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.restrictFun_pullAway_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.frameUnit_eq_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.xMul_pow_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.exists_eq_pullAway_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.basicOpen_frameUnit_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.exists_pow_mul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.pullAway_pow`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.frac_congr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.frameUnit_pow_mul_pullAway_frac`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam_mem`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam_apply_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam_apply_ne`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam_smul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.xMul_unitFam`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.prod_X_pow_mul_mem`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.unitFam_congr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.monMul_unitFam`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.singleHom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.absorb`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.vtx`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.img_vtx`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.globSec`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.secIncl_globSec`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.globCocycle`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.globCocycle_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.apply_eq_of_globSec_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.secMap_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.HMap_zero_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.sat_shift`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.X_pow_mul_mem`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.xMul_pow_unitFam`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.PolySurjBody.apply_eq_of_globSec_vtx_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion` (same contribution).
Other imports: `Mathlib`.
