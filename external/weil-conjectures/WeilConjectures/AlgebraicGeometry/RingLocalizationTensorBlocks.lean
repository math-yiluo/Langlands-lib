/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.RingPointTensorComparison

/-! # Evaluated blocks of tensoring with one localization complex

Source: Stacks Project, algebraization.tex, Tag 0996; the two-term tensor calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingPointTensorComparison

section TwoRows
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasBinaryBiproducts D]
  (P K : CochainComplex D ℤ) [HomologicalComplex.HasTensor P K]

private def twoRowsInverse (n m : ℤ) (hm : 1 + m = n) :
    (HomologicalComplex.tensorObj P K).X n ⟶
      (P.X 0 ⊗ K.X n) ⊞ (P.X 1 ⊗ K.X m) :=
  HomologicalComplex.mapBifunctorDesc fun i j h ↦
    if hi : i = 0 then
      eqToHom (by have hj : j = n := by change i + j = n at h; omega
                  subst i; subst j; rfl) ≫ biprod.inl
    else if hi : i = 1 then
      eqToHom (by have hj : j = m := by change i + j = n at h; omega
                  subst i; subst j; rfl) ≫ biprod.inr
    else 0

private def twoRowsIso (hP : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i))
    (n m : ℤ) (hm : 1 + m = n) :
    (P.X 0 ⊗ K.X n) ⊞ (P.X 1 ⊗ K.X m) ≅
      (HomologicalComplex.tensorObj P K).X n where
  hom := biprod.desc (HomologicalComplex.ιTensorObj P K 0 n n (zero_add n))
    (HomologicalComplex.ιTensorObj P K 1 m n hm)
  inv := twoRowsInverse P K n m hm
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp [twoRowsInverse, HomologicalComplex.ιTensorObj]
    · simp [twoRowsInverse, HomologicalComplex.ιTensorObj]
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    change i + j = n at h
    by_cases hi : i = 0
    · subst i
      obtain rfl : j = n := by omega
      simp [twoRowsInverse, HomologicalComplex.ιTensorObj]
    · by_cases hi' : i = 1
      · subst i
        obtain rfl : j = m := by omega
        simp [twoRowsInverse, HomologicalComplex.ιTensorObj]
      · exact ((tensorRight (K.X j)).map_isZero (hP i hi hi')).eq_of_src _ _

omit [HasZeroObject D] [HasBinaryBiproducts D] in
private theorem tensorInclusion_d (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj P K p q n h ≫
        (HomologicalComplex.tensorObj P K).d n (n + 1) =
      P.d p (p + 1) ▷ K.X q ≫
        HomologicalComplex.ιTensorObj P K (p + 1) q (n + 1) (by omega) +
      p.negOnePow • (P.X p ◁ K.d q (q + 1) ≫
        HomologicalComplex.ιTensorObj P K p (q + 1) (n + 1) (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _ (show p + 1 + q = n + 1 by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _ (show p + (q + 1) = n + 1 by omega)]
  simp

end TwoRows

section LocalizationRows
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
variable (A : CommRingCat.{u}) (s₀ : A)
private abbrev ringO := CochainComplex.onePointRingSheaf A
private def ringS : ((ringO A).obj ⋙ forget CommRingCat).sections :=
  ⟨fun _ ↦ s₀, fun _ ↦ rfl⟩
private abbrev ringP := ringedLocalizationTwoTerm (ringO A) (ringS A s₀)

private local instance : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
  SheafOfModules.isGrothendieckAbelian _
private local instance : HasColimitsOfSize.{0, 0} (RingSiteModules A) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _
private local instance : MonoidalCategory (RingSiteModules A) :=
  SheafOfModules.monoidalCategory (ringO A)
private local instance : SymmetricCategory (RingSiteModules A) :=
  SheafOfModules.symmetricCategory (ringO A)
private local instance : MonoidalPreadditive (RingSiteModules A) :=
  Classical.choice (SheafOfModules.tensorClosed (ringO A)).1
private local instance : MonoidalClosed (RingSiteModules A) :=
  Classical.choice (SheafOfModules.tensorClosed (ringO A)).2.1

private local instance (K : CochainComplex (RingSiteModules A) ℤ) :
    HomologicalComplex.HasTensor (ringP A s₀) K := by infer_instance

private theorem ringP_support (i : ℤ) (h : i ≠ 0) (h' : i ≠ 1) :
    IsZero ((ringP A s₀).X i) := by
  change IsZero (ringedLocalizationTwoTermX _ _ i)
  simpa [ringedLocalizationTwoTermX, h, h'] using isZero_zero (RingSiteModules A)

private def locEvalIso :
    ModuleCat.of A (Localization.Away s₀) ≅
      (pointEval A).obj (ringedSectionLocalization (ringO A) (ringS A s₀)) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (ringO A)).obj)
  let Q := ringedSectionLocalizationPresheaf (ringO A) (ringS A s₀)
  have : IsIso (adj.unit.app Q) :=
    adj.isIso_unit_app_of_iso (X := ⟨Q, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  exact (PresheafOfModules.evaluation _ point).mapIso (asIso (adj.unit.app Q))

private def rowZeroIso (K : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    (ringP A s₀).X 0 ⊗ K.X n ≅ K.X n :=
  ((eqToIso (ringedLocalizationTwoTermX_zero (ringO A) (ringS A s₀))) ⊗ᵢ
    Iso.refl (K.X n)) ≪≫ λ_ (K.X n)

private def rowOneIso (K : CochainComplex (RingSiteModules A) ℤ) (m : ℤ) :
    (pointEval A).obj ((ringP A s₀).X 1 ⊗ K.X m) ≅
      ModuleCat.of A (Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m)) :=
  (pointEval A).mapIso
    ((eqToIso (ringedLocalizationTwoTermX_one (ringO A) (ringS A s₀))) ⊗ᵢ
      Iso.refl (K.X m)) ≪≫
  (pointTensorIso (ringedSectionLocalization (ringO A) (ringS A s₀)) (K.X m)).symm ≪≫
  ((locEvalIso A s₀).symm ⊗ᵢ Iso.refl _)

private def rowsEquiv (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n) :
    (pointEval A).obj ((HomologicalComplex.tensorObj (ringP A s₀) K).X n) ≃ₗ[A]
      (pointEval A).obj (K.X n) ×
        (Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m)) :=
  ((pointEval A).mapIso (twoRowsIso (ringP A s₀) K (ringP_support A s₀) n m hm).symm ≪≫
    (pointEval A).mapBiprod _ _ ≪≫
    biprod.mapIso ((pointEval A).mapIso (rowZeroIso A s₀ K n)) (rowOneIso A s₀ K m) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

private def rowZeroInclusion (K : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    K.X n ⟶ (HomologicalComplex.tensorObj (ringP A s₀) K).X n :=
  (rowZeroIso A s₀ K n).inv ≫
    HomologicalComplex.ιTensorObj (ringP A s₀) K 0 n n (zero_add n)

private def rowOneInclusion (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n) :
    ringedSectionLocalization (ringO A) (ringS A s₀) ⊗ K.X m ⟶
      (HomologicalComplex.tensorObj (ringP A s₀) K).X n :=
  (eqToHom (ringedLocalizationTwoTermX_one (ringO A) (ringS A s₀)).symm ▷ K.X m) ≫
    HomologicalComplex.ιTensorObj (ringP A s₀) K 1 m n hm

private theorem ringP_d_zero :
    (ringP A s₀).d 0 1 =
      eqToHom (ringedLocalizationTwoTermX_zero (ringO A) (ringS A s₀)) ≫
        ringedSectionLocalizationUnit (ringO A) (ringS A s₀) ≫
          eqToHom (ringedLocalizationTwoTermX_one (ringO A) (ringS A s₀)).symm := by
  change CochainComplex.of.d (ringedLocalizationTwoTermX (ringO A) (ringS A s₀))
    (ringedLocalizationTwoTermD (ringO A) (ringS A s₀)) 0 (0 + 1) = _
  rw [CochainComplex.of_d]
  simp [ringedLocalizationTwoTermD]

private theorem ringP_d_one : (ringP A s₀).d 1 2 = 0 := by
  change CochainComplex.of.d (ringedLocalizationTwoTermX (ringO A) (ringS A s₀))
    (ringedLocalizationTwoTermD (ringO A) (ringS A s₀)) 1 (1 + 1) = _
  rw [CochainComplex.of_d]
  simp [ringedLocalizationTwoTermD]

private theorem rowZeroInclusion_d (K : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    rowZeroInclusion A s₀ K n ≫
        (HomologicalComplex.tensorObj (ringP A s₀) K).d n (n + 1) =
      K.d n (n + 1) ≫ rowZeroInclusion A s₀ K (n + 1) +
      (λ_ (K.X n)).inv ≫
        (ringedSectionLocalizationUnit (ringO A) (ringS A s₀) ▷ K.X n) ≫
          rowOneInclusion A s₀ K (n + 1) n (by omega) := by
  dsimp only [rowZeroInclusion]
  rw [Category.assoc, tensorInclusion_d (ringP A s₀) K 0 n n (zero_add n),
    Preadditive.comp_add]
  simp only [Int.negOnePow_zero, one_smul]
  erw [ringP_d_zero A s₀]
  simp only [rowZeroIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv, eqToIso.inv,
    tensorHom_id, comp_whiskerRight, Category.assoc, rowOneInclusion]
  simp only [← comp_whiskerRight_assoc, eqToHom_refl,
    id_whiskerRight, Category.id_comp]
  erw [Category.id_comp, ← leftUnitor_inv_naturality_assoc]
  exact add_comm _ _

private theorem rowOneInclusion_d (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n) :
    rowOneInclusion A s₀ K n m hm ≫
        (HomologicalComplex.tensorObj (ringP A s₀) K).d n (n + 1) =
      -(ringedSectionLocalization (ringO A) (ringS A s₀) ◁ K.d m (m + 1) ≫
        rowOneInclusion A s₀ K (n + 1) (m + 1) (by omega)) := by
  dsimp only [rowOneInclusion]
  rw [Category.assoc, tensorInclusion_d (ringP A s₀) K 1 m n hm,
    Preadditive.comp_add]
  erw [ringP_d_one A s₀]
  simp only [MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, zero_add,
    Int.negOnePow_one, Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul,
    Preadditive.comp_neg]
  rw [whisker_exchange_assoc]
  rfl

private def rowOneValue (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n) :
    ModuleCat.of A (Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m)) ⟶
      (pointEval A).obj ((HomologicalComplex.tensorObj (ringP A s₀) K).X n) :=
  (rowOneIso A s₀ K m).inv ≫
    (pointEval A).map (HomologicalComplex.ιTensorObj (ringP A s₀) K 1 m n hm)

private theorem biprod_desc_apply {R : Type*} [Ring R] {X Y Z : ModuleCat R}
    (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y) :
    ((ModuleCat.biprodIsoProd X Y).inv ≫ biprod.desc f g) (x, y) = f x + g y := by
  rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
  simp

private theorem rowsEquiv_symm (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n)
    (x : (pointEval A).obj (K.X n))
    (y : Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m)) :
    (rowsEquiv A s₀ K n m hm).symm (x, y) =
      (pointEval A).map (rowZeroInclusion A s₀ K n) x +
        rowOneValue A s₀ K n m hm y := by
  let F := pointEval A
  let e₀ := F.mapIso (rowZeroIso A s₀ K n)
  let e₁ := rowOneIso A s₀ K m
  have he :
      (biprod.mapIso e₀ e₁).inv ≫
          (F.mapBiprod ((ringP A s₀).X 0 ⊗ K.X n) ((ringP A s₀).X 1 ⊗ K.X m)).inv ≫
          F.map (twoRowsIso (ringP A s₀) K (ringP_support A s₀) n m hm).hom =
        biprod.desc (F.map (rowZeroInclusion A s₀ K n))
          (rowOneValue A s₀ K n m hm) := by
    apply biprod.hom_ext'
    · simp only [biprod.mapIso_inv, biprod.inl_map_assoc, Functor.mapBiprod_inv,
        biprod.inl_desc_assoc, ← F.map_comp]
      change F.map (rowZeroIso A s₀ K n).inv ≫
        F.map (biprod.inl ≫ (twoRowsIso (ringP A s₀) K _ n m hm).hom) = _
      simp only [twoRowsIso, biprod.inl_desc]
      exact (F.map_comp _ _).symm
    · simp only [biprod.mapIso_inv, biprod.inr_map_assoc, Functor.mapBiprod_inv,
        biprod.inr_desc_assoc, ← F.map_comp]
      change e₁.inv ≫ F.map (biprod.inr ≫ (twoRowsIso (ringP A s₀) K _ n m hm).hom) = _
      simp only [twoRowsIso, biprod.inr_desc]
      rfl
  change ((ModuleCat.biprodIsoProd _ _).inv ≫ (biprod.mapIso e₀ e₁).inv ≫
    (F.mapBiprod _ _).inv ≫
      F.map (twoRowsIso (ringP A s₀) K (ringP_support A s₀) n m hm).hom) (x, y) = _
  rw [he]
  exact biprod_desc_apply (R := A) (Y := ModuleCat.of A
    (Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m))) _ _ x y

private theorem locEvalIso_unit (r : A) :
    (ringedSectionLocalizationUnit (ringO A) (ringS A s₀)).val.app point r =
      (locEvalIso A s₀).hom (algebraMap A (Localization.Away s₀) r) := by
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
    (ringedSectionLocalizationPresheaf (ringO A) (ringS A s₀))).app point
    (r • (1 : Localization.Away s₀)) = _
  congr 1
  simp [Algebra.smul_def]

attribute [local irreducible] rowsEquiv rowOneValue locEvalIso

private theorem rowOneValue_eq (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n) :
    rowOneValue A s₀ K n m hm =
      ((locEvalIso A s₀).hom ⊗ₘ 𝟙 ((pointEval A).obj (K.X m))) ≫
        (pointTensorIso (ringedSectionLocalization (ringO A) (ringS A s₀)) (K.X m)).hom ≫
          (pointEval A).map (rowOneInclusion A s₀ K n m hm) := by
  simp only [rowOneValue, rowOneIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
    Iso.refl_inv, Functor.mapIso_inv, eqToIso.inv, rowOneInclusion, tensorHom_id,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, Category.assoc]

private theorem rowOneValue_d (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n)
    (y : Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m)) :
    (pointEval A).map ((HomologicalComplex.tensorObj (ringP A s₀) K).d n (n + 1))
        (rowOneValue A s₀ K n m hm y) =
      -rowOneValue A s₀ K (n + 1) (m + 1) (by omega)
        (TensorProduct.map LinearMap.id ((K.d m (m + 1)).val.app point).hom y) := by
  rw [rowOneValue_eq]
  change (pointEval A).map ((HomologicalComplex.tensorObj (ringP A s₀) K).d n (n + 1))
    ((pointEval A).map (rowOneInclusion A s₀ K n m hm) _) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, rowOneInclusion_d, Functor.map_neg]
  change -((pointEval A).map (rowOneInclusion A s₀ K (n + 1) (m + 1) _)
    ((pointEval A).map (_ ◁ K.d m (m + 1)) _)) = _
  rw [show _ ◁ K.d m (m + 1) = (𝟙 _ ⊗ₘ K.d m (m + 1)) from (id_tensorHom _ _).symm]
  erw [pointTensorIso_natural A (𝟙 (ringedSectionLocalization (ringO A) (ringS A s₀)))
    (K.d m (m + 1))]
  rw [rowOneValue_eq]
  have hcomm : TensorProduct.map
    (LinearMap.id : (pointEval A).obj (ringedSectionLocalization (ringO A) (ringS A s₀)) →ₗ[A]
      (pointEval A).obj (ringedSectionLocalization (ringO A) (ringS A s₀)))
    ((K.d m (m + 1)).val.app point).hom
    (TensorProduct.map ((locEvalIso A s₀).hom).hom
      (LinearMap.id : (pointEval A).obj (K.X m) →ₗ[A] (pointEval A).obj (K.X m)) y) =
    TensorProduct.map ((locEvalIso A s₀).hom).hom
      (LinearMap.id : (pointEval A).obj (K.X (m + 1)) →ₗ[A]
        (pointEval A).obj (K.X (m + 1)))
      (TensorProduct.map (LinearMap.id : Localization.Away s₀ →ₗ[A] Localization.Away s₀)
        ((K.d m (m + 1)).val.app point).hom y) := by
    simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
  exact congrArg (fun t ↦ -((pointEval A).map
    (rowOneInclusion A s₀ K (n + 1) (m + 1) (by omega)))
      ((pointTensorIso (ringedSectionLocalization (ringO A) (ringS A s₀))
        (K.X (m + 1))).hom t)) hcomm

private theorem rowOneValue_one (K : CochainComplex (RingSiteModules A) ℤ)
    (n : ℤ) (x : (pointEval A).obj (K.X n)) :
    rowOneValue A s₀ K (n + 1) n (by omega) (1 ⊗ₜ[A] x) =
      (pointEval A).map ((λ_ (K.X n)).inv ≫
        ringedSectionLocalizationUnit (ringO A) (ringS A s₀) ▷ K.X n ≫
          rowOneInclusion A s₀ K (n + 1) n (by omega)) x := by
  rw [rowOneValue_eq]
  change (pointEval A).map (rowOneInclusion A s₀ K (n + 1) n _)
      ((pointTensorIso _ (K.X n)).hom ((locEvalIso A s₀).hom 1 ⊗ₜ[A] x)) = _
  have h := pointTensorIso_natural A
    (ringedSectionLocalizationUnit (ringO A) (ringS A s₀)) (𝟙 (K.X n))
    ((1 : A) ⊗ₜ[A] x)
  change (pointEval A).map
    (ringedSectionLocalizationUnit (ringO A) (ringS A s₀) ⊗ₘ 𝟙 (K.X n))
      ((pointTensorIso (ringComplexUnit A) (K.X n)).hom ((1 : A) ⊗ₜ[A] x)) =
    (pointTensorIso _ (K.X n)).hom
      ((ringedSectionLocalizationUnit (ringO A) (ringS A s₀)).val.app point (1 : A) ⊗ₜ[A] x)
    at h
  rw [locEvalIso_unit, map_one] at h
  rw [← h, pointTensorIso_unit, tensorHom_id, Functor.map_comp, Functor.map_comp]
  rfl

private theorem rowZeroValue_d (K : CochainComplex (RingSiteModules A) ℤ)
    (n : ℤ) (x : (pointEval A).obj (K.X n)) :
    (pointEval A).map ((HomologicalComplex.tensorObj (ringP A s₀) K).d n (n + 1))
        ((pointEval A).map (rowZeroInclusion A s₀ K n) x) =
      (pointEval A).map (rowZeroInclusion A s₀ K (n + 1))
        ((K.d n (n + 1)).val.app point x) +
      rowOneValue A s₀ K (n + 1) n (by omega) (1 ⊗ₜ[A] x) := by
  rw [rowOneValue_one]
  exact congrArg (fun f ↦ (pointEval A).map f x) (rowZeroInclusion_d A s₀ K n)

private theorem rowsEquiv_d (K : CochainComplex (RingSiteModules A) ℤ)
    (n m : ℤ) (hm : 1 + m = n)
    (x : (pointEval A).obj (K.X n))
    (y : Localization.Away s₀ ⊗[A] (pointEval A).obj (K.X m)) :
    (pointEval A).map ((HomologicalComplex.tensorObj (ringP A s₀) K).d n (n + 1))
        ((rowsEquiv A s₀ K n m hm).symm (x, y)) =
      (rowsEquiv A s₀ K (n + 1) n (by omega)).symm
        ((K.d n (n + 1)).val.app point x,
          (1 : Localization.Away s₀) ⊗ₜ[A] x - TensorProduct.map LinearMap.id
            ((K.d m n).val.app point).hom y) := by
  obtain rfl : n = m + 1 := by omega
  rw [rowsEquiv_symm, map_add, rowZeroValue_d, rowOneValue_d, rowsEquiv_symm, map_sub]
  abel

private theorem rowZeroInclusion_aug (K : CochainComplex (RingSiteModules A) ℤ)
    (a : K ⟶ ringComplexSingle A) :
    rowZeroInclusion A s₀ K 0 ≫
        (HomologicalComplex.tensorHom
          (ringedLocalizationTwoTermAugmentation (ringO A) (ringS A s₀)) a ≫
          (HomologicalComplex.leftUnitor (ringComplexSingle A)).hom).f 0 = a.f 0 := by
  rw [HomologicalComplex.comp_f]
  apply (cancel_mono ((HomologicalComplex.leftUnitor (ringComplexSingle A)).inv.f 0)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    Category.comp_id]
  dsimp only [rowZeroInclusion]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  change _ = a.f 0 ≫ (HomologicalComplex.leftUnitor' (ringComplexSingle A)).inv 0
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [rowZeroIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv, eqToIso.inv,
    tensorHom_id, Category.assoc]
  change (λ_ (K.X 0)).inv ≫ eqToHom _ ▷ K.X 0 ≫
    ((eqToHom _ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv) ▷ K.X 0) ≫
    _ ◁ a.f 0 ≫ _ = _
  simp only [← comp_whiskerRight_assoc,
    eqToHom_refl, Category.id_comp]
  erw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  rfl

end LocalizationRows

/-- Evaluation of the two nonzero rows of a localization tensor total.
Source: Stacks Project, algebraization.tex, Tag 0996, tensor presentation of the
extended complex, and the tensor differential convention of More on Algebra,
section-alternating-cech.
(auxiliary; not a blueprint node).

Proof: on the one-object bottom-topology site every presheaf is a sheaf.
The unit of sheafification and the sectionwise tensor comparison are therefore
isomorphisms. Identify the evaluated degree-zero term of the first factor with A,
and its degree-one term with S=A[1/s]. The coproduct defining the tensor total has
only these two possibly nonzero summands. The coproduct universal property,
the unit isomorphism A tensor M = M, and the evaluated tensor comparison give c.
In degree zero the second summand is S tensor K^{-1}=0, by hneg, giving z.
The tensor augmentation restricts to the tail augmentation on the first row
and is zero on the second row; this proves the augmentation equation.
For the differential use the inclusion formula for the total tensor differential:
on row zero it is d_K together with localization, which evaluates to x maps to
1 tensor x; on row one it is minus 1 tensor d_K, since (-1)^1=-1.
There is no row-two term. These formulas give the two displayed block equations.
All comparisons use universal properties, so no element or denominator is cancelled;
the same construction works for s=0 and the zero ring. -/
theorem ringLocalizationTensor_blocks (A : CommRingCat.{u}) (s₀ : A)
    (K : CochainComplex (RingSiteModules A) ℤ) (a : K ⟶ ringComplexSingle A)
    (hneg : ∀ n : ℤ, n < 0 → Limits.IsZero (K.X n)) :
    let O := CochainComplex.onePointRingSheaf A
    letI : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let s : (O.obj ⋙ forget CommRingCat).sections := ⟨fun _ ↦ s₀, fun _ ↦ rfl⟩
    let P := ringedLocalizationTwoTerm O s
    let L := HomologicalComplex.tensorObj P K
    let b : L ⟶ ringComplexSingle A :=
      HomologicalComplex.tensorHom (ringedLocalizationTwoTermAugmentation O s) a ≫
        (HomologicalComplex.leftUnitor (ringComplexSingle A)).hom
    let M (n : ℕ) : ModuleCat.{u} A := (K.X (n : ℤ)).val.obj (op ⟨PUnit.unit⟩)
    let S := Localization.Away s₀
    ∃ (z : (L.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] M 0)
      (c : ∀ q : ℕ, (L.X ((q + 1 : ℕ) : ℤ)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
        M (q + 1) × (S ⊗[A] M q)),
      (∀ x, ringComplexAugmentationValue b x = ringComplexAugmentationValue a (z x)) ∧
      (∀ x, c 0 ((L.d 0 1).val.app (op ⟨PUnit.unit⟩) x) =
        ((K.d 0 1).val.app (op ⟨PUnit.unit⟩) (z x), 1 ⊗ₜ[A] z x)) ∧
      (∀ (q : ℕ) (x : (L.X ((q + 1 : ℕ) : ℤ)).val.obj (op ⟨PUnit.unit⟩)),
        c (q + 1) ((L.d ((q + 1 : ℕ) : ℤ) ((q + 2 : ℕ) : ℤ)).val.app
            (op ⟨PUnit.unit⟩) x) =
          ((K.d ((q + 1 : ℕ) : ℤ) ((q + 2 : ℕ) : ℤ)).val.app
            (op ⟨PUnit.unit⟩) (c q x).1,
          1 ⊗ₜ[A] (c q x).1 - TensorProduct.map (LinearMap.id : S →ₗ[A] S)
            ((K.d (q : ℤ) ((q + 1 : ℕ) : ℤ)).val.app (op ⟨PUnit.unit⟩)).hom
              (c q x).2)) := by
  dsimp only
  let O := CochainComplex.onePointRingSheaf A
  let : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let F := pointEval A
  let L := HomologicalComplex.tensorObj (ringP A s₀) K
  let b : L ⟶ ringComplexSingle A :=
    HomologicalComplex.tensorHom
      (ringedLocalizationTwoTermAugmentation (ringO A) (ringS A s₀)) a ≫
      (HomologicalComplex.leftUnitor (ringComplexSingle A)).hom
  change ∃ (z : F.obj (L.X 0) ≃ₗ[A] F.obj (K.X 0))
    (c : ∀ q : ℕ, F.obj (L.X ((q + 1 : ℕ) : ℤ)) ≃ₗ[A]
      F.obj (K.X ((q + 1 : ℕ) : ℤ)) × (Localization.Away s₀ ⊗[A] F.obj (K.X (q : ℤ)))),
    (∀ x, ringComplexAugmentationValue b x = ringComplexAugmentationValue a (z x)) ∧
    (∀ x, c 0 (F.map (L.d 0 1) x) =
      (F.map (K.d 0 1) (z x), (1 : Localization.Away s₀) ⊗ₜ[A] z x)) ∧
    (∀ (q : ℕ) (x : F.obj (L.X ((q + 1 : ℕ) : ℤ))),
      c (q + 1) (F.map (L.d ((q + 1 : ℕ) : ℤ) ((q + 2 : ℕ) : ℤ)) x) =
        (F.map (K.d ((q + 1 : ℕ) : ℤ) ((q + 2 : ℕ) : ℤ)) (c q x).1,
          (1 : Localization.Away s₀) ⊗ₜ[A] (c q x).1 - TensorProduct.map
            (LinearMap.id : Localization.Away s₀ →ₗ[A] Localization.Away s₀)
            (F.map (K.d (q : ℤ) ((q + 1 : ℕ) : ℤ))).hom (c q x).2))
  have hnegEval : IsZero (F.obj (K.X (-1))) := F.map_isZero (hneg (-1) (by decide))
  have hnegTensor : IsZero (ModuleCat.of A (Localization.Away s₀) ⊗ F.obj (K.X (-1))) :=
    (tensorLeft (ModuleCat.of A (Localization.Away s₀))).map_isZero hnegEval
  let := ModuleCat.subsingleton_of_isZero hnegTensor
  let : Unique (Localization.Away s₀ ⊗[A] F.obj (K.X (-1))) :=
    ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let z := (rowsEquiv A s₀ K 0 (-1) (by decide)).trans LinearEquiv.prodUnique
  let c (q : ℕ) := rowsEquiv A s₀ K ((q + 1 : ℕ) : ℤ) (q : ℤ) (by omega)
  have hz (x : F.obj ((HomologicalComplex.tensorObj (ringP A s₀) K).X 0)) :
      (pointEval A).map (rowZeroInclusion A s₀ K 0) (z x) = x := by
    have h := rowsEquiv_symm A s₀ K 0 (-1) (by decide) (z x) 0
    have hc : (z x, 0) = rowsEquiv A s₀ K 0 (-1) (by decide) x := by
      apply Prod.ext
      · change ((rowsEquiv A s₀ K 0 (-1) (by decide)) x).1 = _
        rfl
      · exact Subsingleton.elim _ _
    rw [hc] at h
    simpa only [map_zero, add_zero, LinearEquiv.symm_apply_apply] using h.symm
  refine ⟨z, c, ?_, ?_, ?_⟩
  · intro x
    conv_lhs => rw [← hz x]
    exact congrArg (fun f ↦ ((f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (ringComplexUnit A)).hom).val.app point) (z x)) (rowZeroInclusion_aug A s₀ K a)
  · intro x
    have h := rowsEquiv_d A s₀ K 0 (-1) (by decide) (z x) 0
    rw [rowsEquiv_symm, map_zero, add_zero, hz] at h
    apply (c 0).eq_symm_apply.mp
    simp only [map_zero, sub_zero] at h
    convert h using 1 <;> rfl
  · intro q
    dsimp only [c]
    intro x
    let e := rowsEquiv A s₀ K ((q : ℤ) + 1) (q : ℤ) (by omega)
    have h := rowsEquiv_d A s₀ K ((q : ℤ) + 1) (q : ℤ) (by omega) (e x).1 (e x).2
    have hx : (rowsEquiv A s₀ K ((q : ℤ) + 1) (q : ℤ) (by omega)).symm
        ((e x).1, (e x).2) = x := e.symm_apply_apply x
    rw [hx] at h
    apply (rowsEquiv A s₀ K ((q : ℤ) + 1 + 1) ((q : ℤ) + 1) (by omega)).eq_symm_apply.mp
    exact h

end CategoryTheory
