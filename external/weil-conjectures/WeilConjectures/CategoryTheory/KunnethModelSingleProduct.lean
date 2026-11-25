/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.BoundedKunnethSpectralSequence
public import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # The cocycle product with a single coefficient complex
Source: Stacks Project, Tag 0H7Z, equation simple-tor-product.
(blueprint: lem-pur-kunneth-model-single-product)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory

variable (R : Type u) [CommRing R]

private theorem cycle_element_condition
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) (z : P.cycles q) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ ((P.iCycles q).hom z)) ≫
      P.d q (q + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (P.d q (q + 1)).hom (r • (P.iCycles q).hom z) = 0
  rw [map_smul]
  have hz : (P.d q (q + 1)).hom ((P.iCycles q).hom z) = 0 := by
    exact congrArg (fun f : P.cycles q ⟶ P.X (q + 1) ↦ f.hom z)
      (P.iCycles_d q (q + 1))
  rw [hz, smul_zero]

private theorem single_element_condition (M : ModuleCat.{u} R) (a : M) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv.hom a)) ≫
      ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M).d 0 (0 + 1) = 0 := by
  simp

/-- The cochain map induced by a coefficient element, via the ordinary tensor unit.
Source: Stacks Project, Tag 0H7Z, simple-tor-product.
(blueprint: lem-pur-kunneth-model-single-product) -/
def modelCoefficientAction (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (a : M) :
    P ⟶ P ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M :=
  (ρ_ P).inv ≫ P ◁ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M a))

private theorem modelCoefficientAction_f
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (a : M) (q : ℤ) :
    (modelCoefficientAction R P M a).f q =
      (ρ_ (P.X q)).inv ≫ (P.X q ◁
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R M a) ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv)) ≫
      HomologicalComplex.ιTensorObj P
        ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M) q 0 q (by simp) := by
  change (HomologicalComplex.rightUnitor' P).inv q ≫ _ = _
  rw [HomologicalComplex.rightUnitor'_inv]
  change _ ≫ _ ≫ HomologicalComplex.ιTensorObj P _ q 0 q _ ≫
    (HomologicalComplex.tensorHom (𝟙 P)
      ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map _)).f q = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp]
  change _ ≫ P.X q ◁ _ ≫ P.X q ◁ _ ≫ _ = _
  rw [← whiskerLeft_comp_assoc]
  congr 2

/-- The cocycle product with a coefficient element: the coefficient action sends the class
of a cocycle `z` to the class of the cocycle `z ⊗ a`.
Source: Stacks Project, Tag 0H7Z, simple-tor-product.
(blueprint: lem-pur-kunneth-model-single-product) -/
theorem homologyMap_modelCoefficientAction_homologyπ
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (a : M) (q : ℤ)
    (z : P.cycles q) :
    ∃ c : (P ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M).cycles q,
      ((P ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M).iCycles q).hom c =
        (HomologicalComplex.ιTensorObj P
          ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M) q 0 q
            (by simp)).hom ((P.iCycles q).hom z ⊗ₜ[R]
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv.hom a) ∧
      (HomologicalComplex.homologyMap (modelCoefficientAction R P M a) q).hom
          ((P.homologyπ q).hom z) =
        ((P ⊗ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M).homologyπ q).hom
          c := by
  refine ⟨HomologicalComplex.cyclesMap (modelCoefficientAction R P M a) q z, ?_, ?_⟩
  · rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply,
      modelCoefficientAction_f]
    simp only [ModuleCat.of_coe, whiskerLeft_comp, Category.assoc, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply, ConcreteCategory.hom_ofHom]
    erw [LinearMap.toSpanSingleton_apply, one_smul]
    rfl
  · rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]

end CategoryTheory
