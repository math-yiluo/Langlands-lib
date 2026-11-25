/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AmbientAssociator
public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AbstractDescent
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory

/-! # Derived coherence of the ordinary coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.FdIntegralScalarForward

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u})

set_option hygiene false in
local notation "𝒪 " h:max => integralOrdinaryScalar l (pbcFiniteField.{u} l Ω _)
  (pbcFiniteField.{u} l Ω _) (pbcFiniteFieldInclusion l Ω h) T

set_option hygiene false in
local notation "𝓉 " E:max => fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T

set_option hygiene false in
local notation "𝒳 " h:max => pbcExtend (pbcCompletedScalarMap l Ω T h)

set_option linter.flexible false in
private theorem otc_f {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) (n : ℤ) :
    ((FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T h o).hom.app P).f n =
      (oc l Ω T h o).hom.app (P.X n) := by
  simp [FdIntegralOrdinaryScalarModel.ordinaryTransportComplex,
    FdOrdinaryScalarTransport.complex, oc]

private theorem iso_cocycle_hom {C : Type*} [Category C] {A B D E F : C} (f : B ≅ A)
    (g : D ≅ B) (m : D ⟶ F) (x : A ⟶ E) (n : F ≅ E)
    (h : f.inv ≫ g.inv ≫ m = x ≫ n.inv) : g.hom ≫ f.hom ≫ x = m ≫ n.hom := by
  have hx : x = f.inv ≫ g.inv ≫ m ≫ n.hom := by
    have h2 := congrArg (· ≫ n.hom) h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    exact h2.symm
  rw [hx]
  simp

private theorem gODcomp_fac
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (κ : E →ₐ[ℚ_[l]] M) (hκ : j.comp ι = κ)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (integralOrdinaryDerivedScalarComp l E L ι T M j ≪≫ eqToIso (congrArg
        (fun ι ↦ integralOrdinaryDerivedScalar l E M ι T) hκ)).hom.app (DerivedCategory.Q.obj P) ≫
      (integralOrdinaryScalar l E M κ T).mapDerivedCategoryFactors.hom.app P =
    (integralOrdinaryScalar l L M j T).mapDerivedCategory.map
        ((integralOrdinaryScalar l E L ι T).mapDerivedCategoryFactors.hom.app P) ≫
      (integralOrdinaryScalar l L M j T).mapDerivedCategoryFactors.hom.app
        (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (integralOrdinaryScalarComp l E L ι T M j ≪≫ eqToIso (congrArg
          (fun ι ↦ integralOrdinaryScalar l E M ι T) hκ)) (.up ℤ)).hom.app P) := by
  subst hκ
  simp only [eqToIso_refl, Iso.trans_refl]
  rw [integralOrdinaryDerivedScalarComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  have hc' := Functor.mapDerivedCategoryCompIso_hom_app_factors (integralOrdinaryScalar l E L ι T)
    (integralOrdinaryScalar l L M j T) P
  have hc2 : ((integralOrdinaryScalar l E L ι T).mapDerivedCategoryCompIso
      (integralOrdinaryScalar l L M j T)).hom.app (DerivedCategory.Q.obj P) ≫
      (integralOrdinaryScalar l E L ι T ⋙ integralOrdinaryScalar l L M j T
        ).mapDerivedCategoryFactors.hom.app P =
      (integralOrdinaryScalar l L M j T).mapDerivedCategory.map
        ((integralOrdinaryScalar l E L ι T).mapDerivedCategoryFactors.hom.app P) ≫
      (integralOrdinaryScalar l L M j T).mapDerivedCategoryFactors.hom.app
        (((integralOrdinaryScalar l E L ι T).mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [← hc', Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hc2]
  simp only [Category.assoc]
  rfl


variable [IsNoetherian T]

private theorem oc_cocycle_hom {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (oh : FdOrdinaryScalarTransport l Ω T h) (ok : FdOrdinaryScalarTransport l Ω T k)
    (ohk : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) :
    (oc l Ω T k ok).hom.app ((𝒪 h).obj N) ≫ (𝒳 k).map ((oc l Ω T h oh).hom.app N) ≫
        (Xcomp l Ω T h k).hom.app ((𝓉 E).obj N) =
      (𝓉 M).map ((Ocomp l Ω T h k).hom.app N) ≫ (oc l Ω T (h.trans k) ohk).hom.app N :=
  iso_cocycle_hom ((𝒳 k).mapIso ((oc l Ω T h oh).app N)) ((oc l Ω T k ok).app ((𝒪 h).obj N))
    _ _ ((oc l Ω T (h.trans k) ohk).app N)
    (comparison_cocycle l Ω T h k (oc l Ω T h oh) (oc l Ω T k ok) (oc l Ω T (h.trans k) ohk)
      (Ocomp l Ω T h k) (Xcomp l Ω T h k) (oc_inv_tensor l Ω T h oh) (oc_inv_tensor l Ω T k ok)
      (oc_inv_tensor l Ω T (h.trans k) ohk) (Ocomp_tensor l Ω T h k) (Xcomp_tensor l Ω T h k) N)

/-- The ordinary derived balancing with the direct field inclusion. -/
def ODcomp {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) T ⋙
      integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω L) (pbcFiniteField.{u} l Ω M)
        (pbcFiniteFieldInclusion l Ω k) T ≅
    integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
        (pbcFiniteFieldInclusion l Ω (h.trans k)) T :=
  integralOrdinaryDerivedScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
      (pbcFiniteFieldInclusion l Ω k) ≪≫
    eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) ι T) (inclusion_comp l Ω h k))

theorem ODcomp_eq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    ODcomp l Ω T h k = integralOrdinaryDerivedScalarComp l
      (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
      (pbcFiniteFieldInclusion l Ω k) ≪≫
    eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) ι T) (inclusion_comp l Ω h k)) := rfl

theorem ODcomp_app_eq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
    (X : DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) T)) :
    (ODcomp l Ω T h k).hom.app X = (integralOrdinaryDerivedScalarComp l
      (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
      (pbcFiniteFieldInclusion l Ω k) ≪≫
    eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) ι T) (inclusion_comp l Ω h k))).hom.app X := by
  rw [ODcomp_eq]

private theorem counit_isIso {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ) :
    IsIso ((pbcCounitNT (pbcCompletedScalarMap l Ω T h)).app P) := by
  rw [pbcCounitNT_app]
  have hφ := pbcStageCoefficientMap_eq l Ω T h
  have : PreservesFiniteLimits (pbcExtend (pbcCompletedScalarMap l Ω T h)) := by
    rw [hφ]
    exact (scalarExtension_exact l _ _ (pbcFiniteFieldInclusion l Ω h) T).1
  have : PreservesFiniteColimits (pbcExtend (pbcCompletedScalarMap l Ω T h)) := by
    rw [hφ]
    exact (scalarExtension_exact l _ _ (pbcFiniteFieldInclusion l Ω h) T).2
  obtain ⟨a, -, ha⟩ := FdIntegralOrdinaryScalarModel.ambientExactModel_at l _ _
    (pbcFiniteFieldInclusion l Ω h) T _ hφ
  rw [← ha P]
  infer_instance

theorem ODcomp_fac {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    (ODcomp l Ω T h k).hom.app (DerivedCategory.Q.obj P) ≫
      (𝒪 (h.trans k)).mapDerivedCategoryFactors.hom.app P =
    (𝒪 k).mapDerivedCategory.map ((𝒪 h).mapDerivedCategoryFactors.hom.app P) ≫
      (𝒪 k).mapDerivedCategoryFactors.hom.app (((𝒪 h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Ocomp l Ω T h k)
        (.up ℤ)).hom.app P) := by
  rw [ODcomp_app_eq, Ocomp_eq]
  exact gODcomp_fac l T _ _ _ _ _ _ (inclusion_comp l Ω h k) P

private theorem chain_cocycle_gen {V₁ V₂ V₃ W₁ W₂ W₃ : Type*} [Category V₁] [Category V₂]
    [Category V₃] [Category W₁] [Category W₂] [Category W₃] [Preadditive V₁] [Preadditive V₂]
    [Preadditive V₃] [Preadditive W₁] [Preadditive W₂] [Preadditive W₃]
    (o₁ : V₁ ⥤ V₂) (o₂ : V₂ ⥤ V₃) (o₁₂ : V₁ ⥤ V₃) (t₁ : V₁ ⥤ W₁) (t₂ : V₂ ⥤ W₂)
    (t₃ : V₃ ⥤ W₃) (x₁ : W₁ ⥤ W₂) (x₂ : W₂ ⥤ W₃) (x₁₂ : W₁ ⥤ W₃)
    [o₁.Additive] [o₂.Additive] [o₁₂.Additive] [t₁.Additive] [t₂.Additive] [t₃.Additive]
    [x₁.Additive] [x₂.Additive] [x₁₂.Additive]
    (c₁ : o₁ ⋙ t₂ ≅ t₁ ⋙ x₁) (c₂ : o₂ ⋙ t₃ ≅ t₂ ⋙ x₂) (c₁₂ : o₁₂ ⋙ t₃ ≅ t₁ ⋙ x₁₂)
    (C₁ : o₁.mapHomologicalComplex (.up ℤ) ⋙ t₂.mapHomologicalComplex (.up ℤ) ≅
      t₁.mapHomologicalComplex (.up ℤ) ⋙ x₁.mapHomologicalComplex (.up ℤ))
    (C₂ : o₂.mapHomologicalComplex (.up ℤ) ⋙ t₃.mapHomologicalComplex (.up ℤ) ≅
      t₂.mapHomologicalComplex (.up ℤ) ⋙ x₂.mapHomologicalComplex (.up ℤ))
    (C₁₂ : o₁₂.mapHomologicalComplex (.up ℤ) ⋙ t₃.mapHomologicalComplex (.up ℤ) ≅
      t₁.mapHomologicalComplex (.up ℤ) ⋙ x₁₂.mapHomologicalComplex (.up ℤ))
    (hC₁ : ∀ P n, (C₁.hom.app P).f n = c₁.hom.app (P.X n))
    (hC₂ : ∀ P n, (C₂.hom.app P).f n = c₂.hom.app (P.X n))
    (hC₁₂ : ∀ P n, (C₁₂.hom.app P).f n = c₁₂.hom.app (P.X n))
    (Oc : o₁ ⋙ o₂ ≅ o₁₂) (Xc : x₁ ⋙ x₂ ≅ x₁₂)
    (hmod : ∀ N, c₂.hom.app (o₁.obj N) ≫ x₂.map (c₁.hom.app N) ≫ Xc.hom.app (t₁.obj N) =
      t₃.map (Oc.hom.app N) ≫ c₁₂.hom.app N)
    (P : CochainComplex V₁ ℤ) :
    C₂.hom.app ((o₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (x₂.mapHomologicalComplex (.up ℤ)).map (C₁.hom.app P) ≫
        (Functor.mapHomologicalComplexCompIso Xc (.up ℤ)).hom.app
          ((t₁.mapHomologicalComplex (.up ℤ)).obj P) =
      (t₃.mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso Oc (.up ℤ)).hom.app P) ≫ C₁₂.hom.app P := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hC₁, hC₂, hC₁₂,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  exact hmod (P.X n)


private theorem chain_cocycle {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (oh : FdOrdinaryScalarTransport l Ω T h) (ok : FdOrdinaryScalarTransport l Ω T k)
    (ohk : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T k ok).hom.app
        (((𝒪 h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((𝒳 k).mapHomologicalComplex (.up ℤ)).map
        ((FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T h oh).hom.app P) ≫
      (pbcExtendCompC _ _ _ (pbcCompletedScalarMap_comp l Ω T h k)).hom.app
        (((𝓉 E).mapHomologicalComplex (.up ℤ)).obj P) =
    ((𝓉 M).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Ocomp l Ω T h k) (.up ℤ)).hom.app P) ≫
      (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T (h.trans k) ohk).hom.app P := by
  letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
  letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω L) T
  letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω M) T
  exact chain_cocycle_gen _ _ _ _ _ _ _ _ _ (oc l Ω T h oh) (oc l Ω T k ok)
    (oc l Ω T (h.trans k) ohk)
    _ _ _ (otc_f l Ω T h oh) (otc_f l Ω T k ok) (otc_f l Ω T (h.trans k) ohk)
    (Ocomp l Ω T h k) (Xcomp l Ω T h k) (oc_cocycle_hom l Ω T h k oh ok ohk) P

end WeilConjectures.FdIntegralScalarForward
