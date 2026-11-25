/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence
/-! # Tensor mates commute with canonical étale exchange -/
@[expose] public noncomputable section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Etale.PurityTensorExchange
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local instance] Scheme.Etale.essentiallySmall
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
variable (A : Type (w + 1)) [CommRing A] [Finite A]
variable {X Z U V : Scheme.{w}}
variable (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (j : V ⟶ U)
variable [HasCompactification i] [HasCompactification j] [QuasiCompact j]
set_option maxRecDepth 2000
/-- The canonical inverse exceptional exchange commutes with tensor mates. -/
theorem tensorMap_restriction (sq : IsPullback j v u i)
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))) :
    (upperStar (ModuleCat A) v).leftDerivedFunctor.map
      (rightDerivedUpperShriekTensorMap i K L) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq.flip).app (K ⊗ L) ≫
      (rightDerivedUpperShriek A j).map
        (leftDerivedUpperStarTensorIso (ModuleCat A) u K L).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat A) v
      ((rightDerivedUpperShriek A i).obj K)
      ((upperStar (ModuleCat A) i).leftDerivedFunctor.obj L)).hom ≫
      (rightDerivedUpperShriekBaseChangeMap A sq.flip).app K ▷
        (upperStar (ModuleCat A) v).leftDerivedFunctor.obj
          ((upperStar (ModuleCat A) i).leftDerivedFunctor.obj L) ≫
      (rightDerivedUpperShriek A j).obj
        ((upperStar (ModuleCat A) u).leftDerivedFunctor.obj K) ◁
          derivedSquareUpperStarIsoInvApp (ModuleCat A) sq.flip.toCommSq L ≫
      rightDerivedUpperShriekTensorMap j
        ((upperStar (ModuleCat A) u).leftDerivedFunctor.obj K)
        ((upperStar (ModuleCat A) u).leftDerivedFunctor.obj L) := by
  have hi : IsIso (rightDerivedLowerShriekBaseChangeMap A sq.flip) :=
    isIso_rightDerivedLowerShriekBaseChangeMap A sq.flip
  have h := Adjunction.projectionTensorMap_mateEquiv
    (F := (upperStar (ModuleCat A) i).leftDerivedFunctor)
    (F' := (upperStar (ModuleCat A) j).leftDerivedFunctor)
    (Ga := (upperStar (ModuleCat A) v).leftDerivedFunctor)
    (Gb := (upperStar (ModuleCat A) u).leftDerivedFunctor)
    (rightDerivedUpperShriekAdjunction A i) (rightDerivedUpperShriekAdjunction A j)
    (fun M N ↦ ((projectionMap (ModuleCat A) i).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat A) j).app M).app N)
    (projectionMap_app_app_naturality_left j)
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat A) v M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat A) u N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left u φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat A) sq.flip.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap A sq.flip)
    (inv (rightDerivedLowerShriekBaseChangeMap A sq.flip))
    (fun N ↦ by simp [NatIso.isIso_inv_app])
    (by
      intro Z N
      have ht := projectionMap_rightDerivedLowerShriekBaseChangeMap A sq.flip Z N
      simp only [← leftDerivedUpperStarTensorIso_hom,
        derivedTensor_map_app, derivedTensor_obj_map] at ht
      dsimp only [derivedTensor, curriedTensor_obj_obj] at ht
      exact ht) K L
  simpa only [rightDerivedUpperShriekBaseChangeMap, rightDerivedUpperShriekTensorMap,
    lowerShriekRightAdjointTensorMap] using h

attribute [instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

end AlgebraicGeometry.Etale.PurityTensorExchange
