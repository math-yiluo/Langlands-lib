/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar

/-! # Normalized transition equation for localized constant models

This is the normalized-arrow part of the localized constant realization.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
* Stacks Project, Sites, Tag 0H7J
* Stacks Project, Cohomology on Sites, Tag 06YY
* Stacks Project, Categories, Sections 4.2 and 4.27
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/-- Constants, comparison, and the two inverse images, before finite restriction. -/
def lisseTowerConstantInput {X Z T S : Scheme.{u}}
    (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  normalizationConstant S.smallEtaleTopology ⋙
    localProEtaleComparison a (lisseTowerEtaleRing d n) ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d n

/-- Paste the constant, site-comparison, and final scalar squares with explicit
associators. Keeping this construction abstract avoids unfolding coefficient sheaves. -/
def lisseTowerPasteConstantScalar
    {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ E : Type*}
    [Category A₀] [Category A₁] [Category B₀] [Category B₁]
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
    (R : A₀ ⥤ A₁) (S : B₀ ⥤ B₁) (T : C₀ ⥤ C₁)
    (F₀ : A₀ ⥤ B₀) (F₁ : A₁ ⥤ B₁)
    (G₀ : B₀ ⥤ C₀) (G₁ : B₁ ⥤ C₁)
    (L₀ : C₀ ⥤ D₀) (L₁ : C₁ ⥤ D₁) (H₀ : D₀ ⥤ E) (H₁ : D₁ ⥤ E)
    (e : R ⋙ F₁ ≅ F₀ ⋙ S) (f : S ⋙ G₁ ≅ G₀ ⋙ T)
    (h : T ⋙ L₁ ⋙ H₁ ≅ L₀ ⋙ H₀) :
    R ⋙ (F₁ ⋙ G₁ ⋙ L₁) ⋙ H₁ ≅ (F₀ ⋙ G₀ ⋙ L₀) ⋙ H₀ :=
  Functor.isoWhiskerLeft R
      (Functor.associator F₁ (G₁ ⋙ L₁) H₁ ≪≫
        Functor.isoWhiskerLeft F₁ (Functor.associator G₁ L₁ H₁)) ≪≫
    (Functor.associator R F₁ (G₁ ⋙ L₁ ⋙ H₁)).symm ≪≫
    Functor.isoWhiskerRight e (G₁ ⋙ L₁ ⋙ H₁) ≪≫
    Functor.associator F₀ S (G₁ ⋙ L₁ ⋙ H₁) ≪≫
    Functor.isoWhiskerLeft F₀
      ((Functor.associator S G₁ (L₁ ⋙ H₁)).symm ≪≫
        Functor.isoWhiskerRight f (L₁ ⋙ H₁) ≪≫
        Functor.associator G₀ T (L₁ ⋙ H₁) ≪≫ Functor.isoWhiskerLeft G₀ h) ≪≫
    (Functor.associator F₀ (G₀ ⋙ L₀) H₀).symm

/-- The constant coefficient square, with its specified scalar comparisons. -/
def lisseTowerConstantScalarIso {X Z T S : Scheme.{u}}
    (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    normalizationModuleRestrict (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerConstantInput g a b d (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1)) ≅
      lisseTowerConstantInput g a b d n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection g d n) := by
  unfold lisseTowerConstantInput
  exact lisseTowerPasteConstantScalar
    (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
    (normalizationRestrict S.smallEtaleTopology (lisseTowerEtaleQuotient d n))
    (normalizationRestrict (ProEt.topology T) (lisseTowerEtaleQuotient d n))
    (normalizationConstant S.smallEtaleTopology)
    (normalizationConstant S.smallEtaleTopology)
    (localProEtaleComparison a (lisseTowerEtaleRing d n))
    (localProEtaleComparison a (lisseTowerEtaleRing d (n + 1)))
    ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).mapDerivedCategory ⋙
      lisseTowerFixedRealization g d n)
    ((ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).mapDerivedCategory ⋙
      lisseTowerFixedRealization g d (n + 1))
    (pbcDerivedRestrict (constantAdicFiniteProjection g d n))
    (pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1)))
    (normalizationConstantRestrict S.smallEtaleTopology (lisseTowerEtaleQuotient d n)).symm
    (localProEtaleComparisonCoefficients a (lisseTowerEtaleQuotient d n))
    (lisseTowerPulledScalarIso g b d n)

/-- Consecutive algebraic restrictions compose to the fixed restriction. -/
def lisseTowerAlgebraRestrictIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    normalizationModuleRestrict (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerAlgebraForget d (n + 1) ≅ lisseTowerAlgebraForget d n :=
  Functor.mapDerivedCategoryCompIso
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2)))) ≪≫
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2)))
      (lisseTowerEtaleQuotient d n)
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk _).symm)).symm

/-- A natural constant model, transported to completion coefficients. -/
def lisseTowerConstantModelIso {X Z T S : Scheme.{u}}
    (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (model : lisseTowerConstantInput g a b d n ≅ constantAdicQuotientRealization g d n) :
    lisseTowerConstantInput g a b d n ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection g d n) ≅
      lisseTowerAlgebraForget d n ⋙ constantAdicFiniteRealization g d :=
  Functor.isoWhiskerRight model (pbcDerivedRestrict (constantAdicFiniteProjection g d n)) ≪≫
    (constantAdicQuotientRightIso g d n).symm

/-- Compatibility on represented complexes suffices for every derived semilinear arrow. -/
theorem lisseTower_localized_constants_normalization
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (model : ∀ n : ℕ,
      lisseTowerConstantInput g a b d n ≅ constantAdicQuotientRealization g d n)
    (hmodel : ∀ (n : ℕ)
      (K : CochainComplex (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ℤ),
      ((lisseTowerConstantScalarIso g a b d n) ≪≫
        lisseTowerConstantModelIso g a b d n (model n)).hom.app (DerivedCategory.Q.obj K) =
      (Functor.isoWhiskerLeft (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
          (lisseTowerConstantModelIso g a b d (n + 1) (model (n + 1))) ≪≫
        Functor.isoWhiskerRight (lisseTowerAlgebraRestrictIso d n)
          (constantAdicFiniteRealization g d)).hom.app (DerivedCategory.Q.obj K)) :
    ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso ((model j).app N) ≪≫
        ((constantAdicQuotientRightIso g d j).app N).symm
    (H (n + 1)).map ((
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d (n + 1)).map
      (localProEtaleNormalization a (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow S.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (lisseTowerPulledScalarIso g b d n).hom.app
      ((localProEtaleComparison a
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d n k) := by
  intro n E E' k
  let c (j : ℕ) := lisseTowerConstantModelIso g a b d j (model j)
  have h : ((lisseTowerConstantScalarIso g a b d n) ≪≫ c n).hom =
      (Functor.isoWhiskerLeft (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
          (c (n + 1)) ≪≫
        Functor.isoWhiskerRight (lisseTowerAlgebraRestrictIso d n)
          (constantAdicFiniteRealization g d)).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) (.up ℤ))
    exact hmodel n
  have he := NatTrans.congr_app h E'
  have hn := (c (n + 1)).hom.naturality k
  dsimp only [Functor.comp_map] at hn
  have he' := congrArg
    (fun f ↦ (pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1))).map
      ((lisseTowerConstantInput g a b d (n + 1)).map k) ≫ f) he
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he'
  have hnk := congrArg
    (fun f ↦ f ≫ (constantAdicFiniteRealization g d).map
      ((lisseTowerAlgebraRestrictIso d n).hom.app E')) hn
  simp only [Category.assoc] at hnk
  rw [hnk, ← Functor.map_comp] at he'
  simpa only [c, lisseTowerConstantModelIso, lisseTowerConstantScalarIso,
    lisseTowerConstantInput, lisseTowerAlgebraRestrictIso, lisseTowerAlgebraArrow,
    lisseTowerPasteConstantScalar, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id,
    localProEtaleNormalization, normalizationConstantArrow, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, id, Category.assoc] using he'

end AlgebraicGeometry.Scheme
