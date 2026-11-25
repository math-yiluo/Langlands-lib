/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BlowupChart

/-!
# The center `V(I) × {0}` of the blow-up model of the deformation space

For a quasi-coherent ideal `I` on a scheme `X`, the closed subscheme `V(I) × {0}` of the
relative affine line `Spec_X 𝒪_X[t]` is the relative spectrum of `𝒪_X / I` mapping to it by
`p ↦ p(0) mod I`. Its ideal sheaf `I.deformationCenterSheaf` is the center of the blow-up
description of the deformation to the normal cone (blueprint
`definition-deformation-normal-bundle`). Over the chart `Spec Γ(U)[t]` of an affine open `U ⊆ X` it
is `AlgebraicGeometry.AffineBlowup.deformationCenter (I(U)) = I(U) Γ(U)[t] + (t)`
(`ideal_deformationCenterSheaf_chart`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

lemma Scheme.Hom.appLE_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V = f ⁻¹ᵁ U) (x : Γ(Y, U)) : f.appLE U V h.le x = 0 ↔ f.app U x = 0 := by
  subst h
  rw [Scheme.Hom.app_eq_appLE]

namespace Scheme.IdealSheafData

open AffineZariskiSite

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- `𝒪_X[t] ⟶ 𝒪_X / I`, `p ↦ p(0) mod I`. -/
noncomputable def polynomialToQuotient : X.polynomialPresheaf ⟶ I.quotientAlgebra :=
  I.polynomialToQuotientPolynomial ≫ I.quotientPolynomialEvalZero

lemma polynomialToQuotient_app_apply (U : X.AffineZariskiSiteᵒᵖ) (p) :
    (I.polynomialToQuotient.app U).hom p = Ideal.Quotient.mk (I.siteIdeal U.unop) (p.coeff 0) := by
  change Polynomial.eval 0 (Polynomial.map (Ideal.Quotient.mk (I.siteIdeal U.unop)) p) = _
  rw [Polynomial.eval_zero_map, ← Polynomial.coeff_zero_eq_eval_zero]
  rfl

lemma toPolynomialPresheaf_comp_polynomialToQuotient :
    X.toPolynomialPresheaf ≫ I.polynomialToQuotient = I.toQuotientAlgebra := by
  ext U x
  change (I.polynomialToQuotient.app U).hom (Polynomial.C x) = _
  rw [polynomialToQuotient_app_apply, Polynomial.coeff_C_zero]
  rfl

/-- The closed immersion `V(I) × {0} ⟶ Spec_X 𝒪_X[t]`. -/
noncomputable def deformationCenterι : I.quotientSpec ⟶ X.polynomialSpec :=
  relativeGluingMap X.coequifibered_toPolynomialPresheaf I.coequifibered_toQuotientAlgebra
    I.polynomialToQuotient

instance : IsClosedImmersion I.deformationCenterι :=
  relativeGluingMap_of_forall X.coequifibered_toPolynomialPresheaf @IsClosedImmersion
    I.coequifibered_toQuotientAlgebra I.polynomialToQuotient
    I.toPolynomialPresheaf_comp_polynomialToQuotient fun U ↦
      IsClosedImmersion.spec_of_surjective _ fun y ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Polynomial.C r, by
          rw [polynomialToQuotient_app_apply, Polynomial.coeff_C_zero]; rfl⟩

/-- The ideal sheaf of `V(I) × {0}` in `Spec_X 𝒪_X[t]`: the center of the blow-up description of
the deformation to the normal cone (blueprint `definition-deformation-normal-bundle`). -/
noncomputable def deformationCenterSheaf : X.polynomialSpec.IdealSheafData :=
  I.deformationCenterι.ker

variable (X) in
/-- The chart `Spec Γ(U)[t] = (Spec_X 𝒪_X[t]) ×_X U` over an affine open `U`, as an affine
open. -/
noncomputable def polynomialSpecChartOpen (U : X.AffineZariskiSite) :
    X.polynomialSpec.affineOpens :=
  ⟨X.polynomialSpecProj ⁻¹ᵁ U.1, U.2.preimage _⟩

/-- **The center on a chart**: over the chart `Spec Γ(U)[t]`, the ideal of `V(I) × {0}` is
`I(U) Γ(U)[t] + (t)`, via the identification of the sections of the chart with `Γ(U)[t]`. -/
lemma ideal_deformationCenterSheaf_chart (U : X.AffineZariskiSite) :
    I.deformationCenterSheaf.ideal (polynomialSpecChartOpen X U) =
      (AffineBlowup.deformationCenter (I.siteIdeal U)).comap
        (sectionsIso X.coequifibered_toPolynomialPresheaf U).hom.hom := by
  ext x
  rw [deformationCenterSheaf, Scheme.Hom.ker_apply, RingHom.mem_ker, Ideal.mem_comap,
    AffineBlowup.mem_deformationCenter_iff]
  have h := relativeGluingMap_appLE_sectionsIso_hom X.coequifibered_toPolynomialPresheaf
    I.coequifibered_toQuotientAlgebra I.polynomialToQuotient
    I.toPolynomialPresheaf_comp_polynomialToQuotient U
  change (relativeGluingMap X.coequifibered_toPolynomialPresheaf I.coequifibered_toQuotientAlgebra
    I.polynomialToQuotient).app ((relativeGluingData X.coequifibered_toPolynomialPresheaf).toBase
      ⁻¹ᵁ U.1) x = 0 ↔ _
  rw [← Scheme.Hom.appLE_eq_zero_iff _ _ _ (relativeGluingMap_preimage _ _ _
    I.toPolynomialPresheaf_comp_polynomialToQuotient U).symm,
    ← (sectionsIso I.coequifibered_toQuotientAlgebra U).commRingCatIsoToRingEquiv.map_eq_zero_iff]
  change (sectionsIso I.coequifibered_toQuotientAlgebra U).hom
    (I.deformationCenterι.appLE _ _ _ x) = 0 ↔ _
  rw [← CommRingCat.comp_apply]
  erw [h]
  rw [CommRingCat.comp_apply]
  change (I.polynomialToQuotient.app (.op U)).hom _ = 0 ↔ _
  rw [polynomialToQuotient_app_apply]
  exact Ideal.Quotient.eq_zero_iff_mem

end Scheme.IdealSheafData

end AlgebraicGeometry
