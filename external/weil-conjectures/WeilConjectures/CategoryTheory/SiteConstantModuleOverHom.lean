/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.SiteConstantModuleUnit

/-! # Maps out of constant module sheaves on slices

Source: Stacks Project, Modules on Sites, Tags 03CY and 093T.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ] (M N : ModuleCat.{u} Λ)

/-- Evaluate a local morphism on constant sections at the terminal object of the slice. -/
def siteConstantModuleLocalMap (U : C)
    (a : ((siteConstantModuleFunctor J Λ).obj M).over U ⟶
      ((siteConstantModuleFunctor J Λ).obj N).over U) :
    M ⟶ (siteConstantModuleSections J Λ N).obj (op U) :=
  (siteConstantModuleUnitSections J Λ M).app (op U) ≫
    (ModuleCat.restrictScalars
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app (op U)).hom).map
        (a.val.app (op (Over.mk (𝟙 U))))

/-- A map from a constant module sheaf is determined on the constant sections. -/
theorem siteConstantModule_over_hom_ext (U : C)
    (a b : ((siteConstantModuleFunctor J Λ).obj M).over U ⟶
      ((siteConstantModuleFunctor J Λ).obj N).over U)
    (h : ∀ x : M,
      a.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) x) =
      b.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) x)) : a = b := by
  let FM := (siteConstantModuleFunctor J Λ).obj M
  let FN := (siteConstantModuleFunctor J Λ).obj N
  let η := siteConstantModuleUnit J Λ M
  have hlocal (V : Over U) (x : M) :
      a.val.app (op V) (η.app (op V.left) x) =
        b.val.app (op V) (η.app (op V.left) x) := by
    have ha := PresheafOfModules.naturality_apply a.val
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (η.app (op U) x)
    have hb := PresheafOfModules.naturality_apply b.val
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (η.app (op U) x)
    have hn := NatTrans.naturality_apply η V.hom.op x
    change η.app (op V.left) x = FM.val.map V.hom.op (η.app (op U) x) at hn
    change a.val.app (op V) (FM.val.map V.hom.op (η.app (op U) x)) =
      FN.val.map V.hom.op (a.val.app (op (Over.mk (𝟙 U))) (η.app (op U) x)) at ha
    change b.val.app (op V) (FM.val.map V.hom.op (η.app (op U) x)) =
      FN.val.map V.hom.op (b.val.app (op (Over.mk (𝟙 U))) (η.app (op U) x)) at hb
    rw [hn, ha, hb, h x]
  ext V s
  apply FN.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η s)
  intro W f hf
  obtain ⟨x, hx⟩ := hf
  let V' : Over U := Over.mk (f ≫ V.unop.hom)
  have ha := PresheafOfModules.naturality_apply a.val
    (Over.homMk f : V' ⟶ V.unop).op s
  have hb := PresheafOfModules.naturality_apply b.val
    (Over.homMk f : V' ⟶ V.unop).op s
  change a.val.app (op V') (FM.val.map f.op s) = FN.val.map f.op (a.val.app V s) at ha
  change b.val.app (op V') (FM.val.map f.op s) = FN.val.map f.op (b.val.app V s) at hb
  change η.app (op W) x = FM.val.map f.op s at hx
  change FN.val.map f.op (a.val.app V s) = FN.val.map f.op (b.val.app V s)
  rw [← ha, ← hb, ← hx]
  exact hlocal V' x

end CategoryTheory
