/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
import all WeilConjectures.AlgebraicGeometry.HigherDirectImageOverMapCoefficient

/-! # Coefficient factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] moduleAbelianDerivedUpperStarIso

/-- The shifted coefficient part of scalar comparison.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def scalarCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W Y : Scheme.{u}} (h : Y ⟶ W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (moduleAbelianForget Λ Y).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj
          ((moduleAbelianForget Λ W).obj G)))⟦q⟧ :=
  ((moduleAbelianForget Λ Y).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj G)) ≫
    (shiftFunctor _ q).map
      (((moduleAbelianForget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ h G)))

private theorem shift_square
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift D₀ ℤ] [HasShift D₁ ℤ]
    (M : C₀ ⥤ C₁) (VA : C₁ ⥤ D₁) (VB : C₀ ⥤ D₀) (H : D₀ ⥤ D₁)
    [M.CommShift ℤ] [VA.CommShift ℤ] [VB.CommShift ℤ] [H.CommShift ℤ]
    (e : VB ⋙ H ⟶ M ⋙ VA) [NatTrans.CommShift e ℤ]
    (X : C₀) (Y : C₁) (Z : D₀) (T : D₁)
    (m : M.obj X ⟶ Y) (bA : VA.obj Y ⟶ T) (bB : VB.obj X ⟶ Z) (a : H.obj Z ⟶ T)
    (hu : e.app X ≫ VA.map m ≫ bA = H.map bB ≫ a) (q : ℤ) :
    e.app (X⟦q⟧) ≫
      VA.map ((M.commShiftIso q).hom.app X ≫ m⟦q⟧') ≫
      (VA.commShiftIso q).hom.app Y ≫ bA⟦q⟧' =
    H.map ((VB.commShiftIso q).hom.app X ≫ bB⟦q⟧') ≫
      (H.commShiftIso q).hom.app Z ≫ a⟦q⟧' := by
  have hc := NatTrans.shift_app_comm e q X
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  simp only [Functor.map_comp, Category.assoc]
  rw [VA.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% hc]
  rw [H.commShiftIso_hom_naturality_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ H.map ((VB.commShiftIso q).hom.app X) ≫
      (H.commShiftIso q).hom.app (VB.obj X) ≫ t⟦q⟧') hu

private theorem coefficient_unshifted
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A B : Over W) (f : A ⟶ B) :
    (moduleAbelianDerivedUpperStarIso Λ f.left).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor
          0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G)) ≫
      ((moduleAbelianForget Λ A.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)) =
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
      (((moduleAbelianForget Λ B.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ B.hom G))) ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app _) := by
  exact rawModuleScalar_coefficient_unshifted Λ G A B f

/-- (blueprint: lem-sbc-raw-scalar-coefficient-square) -/
theorem rawModuleScalar_coefficient_square
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
  let VA := (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G q
  let bB := scalarCoefficientFactor Λ B.hom G q
  let mT := moduleCoefficientFactor Λ G q A B f
  let aT := abelianCoefficientFactor ((moduleAbelianForget Λ W).obj G) q A B f
  (moduleAbelianDerivedUpperStarIso Λ f.left).hom.app
      (((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦q⟧) ≫
    VA.map mT ≫ bA = H.map bB ≫ aT := by
  have := rawModuleScalar_derivedPullbackIso_commShift Λ f.left
  let M := (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
  let VA := (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus
  let VB := (moduleAbelianForget Λ B.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let e := (moduleAbelianDerivedUpperStarIso Λ f.left).hom
  let X := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)
  let Y := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G)
  let Z := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} B.hom).obj
      ((moduleAbelianForget Λ W).obj G))
  let T := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} A.hom).obj
      ((moduleAbelianForget Λ W).obj G))
  let m : M.obj X ⟶ Y :=
    ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G)
  let bA : VA.obj Y ⟶ T :=
    ((moduleAbelianForget Λ A.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (inv (RawModuleScalarComparison.pullback Λ A.hom G))
  let bB : VB.obj X ⟶ Z :=
    ((moduleAbelianForget Λ B.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (inv (RawModuleScalarComparison.pullback Λ B.hom G))
  let a : H.obj Z ⟶ T :=
    ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app _)
  have hu := coefficient_unshifted Λ G A B f
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let mut inputs := #[]
      for name in [`M, `VA, `VB, `H, `e, `X, `Y, `Z, `T, `m, `bA, `bB, `a, `hu, `q] do
        inputs := inputs.push (← Lean.Meta.getLocalDeclFromUserName name).toExpr
      let proof ← Lean.Meta.mkAppM ``shift_square inputs
      let proof ← Lean.Meta.zetaReduce proof
      coefficientStructuralExact proof

end AlgebraicGeometry.Etale
