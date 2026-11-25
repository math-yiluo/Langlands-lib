/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantReductionTensorModel
public import WeilConjectures.AlgebraicGeometry.ConstantTensorNormalization
public import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedNegativeKoszulLowDegrees

/-! # Strict Koszul tensor and coefficient identifications

Source: Stacks Project, Tags 099M, 093M and 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion.KoszulTensorComparison
open TensorComparison
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local instance] TensorComparison.tensorTower_additive

attribute [local instance] flatConstantCochainMonoidal flatConstantCochainMonoidalStruct
  SheafOfModules.monoidalCategory Functor.preservesZeroMorphisms_of_additive

/-- The koszulEvaluationIso comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
@[irreducible] def koszulEvaluationIso (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (P : Cx O) (n : ℕᵒᵖ) :
    ((ringedKoszulTensorTowerFunctor O r s).obj P).asFunctor.obj n ≅
      P ⊗ ((ringedKoszulDualTower O r s).obj n) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j h
    have hj : i + 1 = j := h
    subst j
    simp [ringedKoszulTensorTowerFunctor, ringedKoszulTensorTowerComplex,
      ringedKoszulTensorTower, CochainComplex.of_d]
    rfl)

/-- The koszulEvaluationTowerIso comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
@[irreducible] def koszulEvaluationTowerIso (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (P : Cx O) :
    ((ringedKoszulTensorTowerFunctor O r s).obj P).asFunctor ≅
      ringedKoszulDualTower O r s ⋙ tensorLeft P :=
  NatIso.ofComponents (koszulEvaluationIso J O r s P) (by
    intro m n f
    apply HomologicalComplex.hom_ext
    intro k
    simp only [HomologicalComplex.comp_f, koszulEvaluationIso,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
    rfl)

/-- The koszulSourceTensorIso comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
@[irreducible] def koszulSourceTensorIso (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (P : Cx O) :
    ((ringedKoszulTensorTowerFunctor O r s).obj (ringedSiteRingComplex O)).asFunctor ⋙
      tensorLeft P ≅ ((ringedKoszulTensorTowerFunctor O r s).obj P).asFunctor := by
  let e : ringedKoszulDualTower O r s ⋙ tensorLeft (ringedSiteRingComplex O) ⋙
      tensorLeft P ≅ ringedKoszulDualTower O r s ⋙ tensorLeft P :=
    NatIso.ofComponents (fun n ↦ (tensorLeft P).mapIso
      (λ_ ((ringedKoszulDualTower O r s).obj n))) (by
        intro m n f
        change (tensorLeft P).map ((tensorLeft (𝟙_ _)).map
            ((ringedKoszulDualTower O r s).map f)) ≫
            (tensorLeft P).map (λ_ ((ringedKoszulDualTower O r s).obj n)).hom =
          (tensorLeft P).map (λ_ ((ringedKoszulDualTower O r s).obj m)).hom ≫
            (tensorLeft P).map ((ringedKoszulDualTower O r s).map f)
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (tensorLeft P).map (leftUnitor_naturality _))
  exact Functor.isoWhiskerRight (koszulEvaluationTowerIso J O r s _) (tensorLeft P) ≪≫
    e ≪≫ (koszulEvaluationTowerIso J O r s P).symm

/-- The source comparison on a tower level uses only unitors and evaluation.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
theorem koszulSourceTensorIso_hom_app (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (P : Cx O) (n : ℕᵒᵖ) :
    (koszulSourceTensorIso J O r s P).hom.app n =
      (tensorLeft P).map (koszulEvaluationIso J O r s (ringedSiteRingComplex O) n).hom ≫
        (tensorLeft P).map (λ_ ((ringedKoszulDualTower O r s).obj n)).hom ≫
        (koszulEvaluationIso J O r s P n).inv := by
  unfold koszulSourceTensorIso koszulEvaluationTowerIso
  rfl

/-- Evaluation of the reconstructed strict tensor is identity in every degree.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
theorem koszulEvaluationIso_inv_f (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (P : Cx O) (n : ℕᵒᵖ) (p : ℤ) :
    (koszulEvaluationIso J O r s P n).inv.f p = 𝟙 _ := by
  unfold koszulEvaluationIso
  rfl

/-- The koszulUnitZero_isIso comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
theorem koszulUnitZero_isIso (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    IsIso ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
      (ringedKoszulDualUnit O r s n).f 0) := by
  have hd : ∃ e : ringedNegativeKoszul O r s n ≅
      (ringedKoszulDualTower O r s).obj (op n),
      ringedNegativeKoszulBasis O r s n ∅ 0 ≫ e.hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r s n).f 0 := by
    cases r with
    | zero =>
        obtain ⟨e, _, he⟩ := ringedNegativeKoszulZeroDuality O s
        exact ⟨e n, he n⟩
    | succ r =>
        obtain ⟨e, _, he⟩ := ringedNegativeKoszulSuccDuality O r s
        exact ⟨e n, he n⟩
  obtain ⟨e, he⟩ := hd
  obtain ⟨e₀, _, h₀, _⟩ := ringedNegativeKoszulLowDegrees O r s n
  rw [← he, ← h₀]
  infer_instance

/-- The reductionModelIso comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
@[irreducible] def reductionModelIso (b : Bool)
    (e : reductionTower J A I b ≅
      tensorTower J (coefficients J A I b)
        ((reductionTower J A I b).obj (𝟙_ (Mod (coefficients J A I b)))))
    (P : Cx (coefficients J A I b)) :
    (reductionComplex J A I b P).asFunctor ≅
      (((tensorTower J (coefficients J A I b)
        ((reductionTower J A I b).obj (𝟙_ (Mod (coefficients J A I b)))))
        |>.mapHomologicalComplex (.up ℤ)).obj P).asFunctor :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P)

/-- The reductionModelIso_hom_f comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
theorem reductionModelIso_hom_f (b : Bool)
    (e : reductionTower J A I b ≅
      tensorTower J (coefficients J A I b)
        ((reductionTower J A I b).obj (𝟙_ (Mod (coefficients J A I b)))))
    (M : Cx (coefficients J A I b)) (n : ℕᵒᵖ) (p : ℤ) :
    ((reductionModelIso J A I b e M).hom.app n).f p =
      (e.hom.app (M.X p)).app n := by
  unfold reductionModelIso
  rfl

/-- The augmentationUnitAt comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
theorem augmentationUnitAt
    (b : Bool) (r : ℕ) (a : Fin r → A)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (P : Cx (coefficients J A I b)) (n : ℕ) (p : ℤ) :
    (ringedKoszulTensorUnitComponent (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) P (op n)).f p ≫
        ((α.app P).f p).app (op n) =
      ((reductionUnit J A I b).app (P.X p)).app (op n) := by
  have h := congrArg (fun f ↦ f.f p ≫
    limit.π ((reductionComplex J A I b P).X p) (op n)) (hα.1 P)
  change _ = (ordinaryUnit_existsUnique J A I b P).exists.choose.f p ≫
    limit.π ((reductionComplex J A I b P).X p) (op n) at h
  rw [(ordinaryUnit_existsUnique J A I b P).exists.choose_spec p n] at h
  change ringedKoszulLimitUnitF (coefficients J A I b) r
      (fun i ↦ algebraSection (baseMap J A I b) (a i)) P p ≫
      limMap ((α.app P).f p) ≫
        limit.π ((reductionComplex J A I b P).X p) (op n) = _ at h
  rw [limMap_π, ← Category.assoc] at h
  unfold ringedKoszulLimitUnitF at h
  dsimp only [id] at h
  rw [limit.lift_π] at h
  exact h

/-- The koszulTensorUnit_f comparison used in the normalized tensor square.
Source: Stacks 099M, 06YN and 0913
(auxiliary; not a blueprint node). -/
theorem koszulTensorUnit_f (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (P : Cx O)
    (n : ℕ) (p : ℤ) :
    (ringedKoszulTensorUnitComponent O r s P (op n)).f p =
      (ρ_ (P.X p)).inv ≫ P.X p ◁
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r s n).f 0) ≫
        HomologicalComplex.ιTensorObj P ((ringedKoszulDualTower O r s).obj (op n))
          p 0 p (add_zero p) := by
  change ((ρ_ P).inv ≫ P ◁ ringedKoszulDualUnit O r s n).f p = _
  rw [HomologicalComplex.comp_f]
  erw [show (ρ_ P).inv.f p = _ from HomologicalComplex.rightUnitor'_inv P p]
  simp only [Category.assoc]
  change _ ≫ _ ≫ (HomologicalComplex.ιTensorObj P (𝟙_ _) p 0 p (add_zero p) ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 P) (ringedKoszulDualUnit O r s n)
      (curriedTensor _) (.up ℤ)).f p) = _
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app,
    id_whiskerRight, curriedTensor_obj_map, whiskerLeft_comp, Category.assoc]
  erw [Category.id_comp]

end CategoryTheory.ConstantCompletion.KoszulTensorComparison
