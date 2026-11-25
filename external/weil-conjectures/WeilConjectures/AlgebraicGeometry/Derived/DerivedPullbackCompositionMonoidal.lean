/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Ring.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem derivedPullbackCompositionTensor
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X Y Z : Scheme.{u}} (uMap : Y ⟶ X) (vMap : Z ⟶ Y)
    [(uMap)^*[A].PreservesFlat] [(vMap)^*[A].PreservesFlat]
    [((vMap ≫ uMap))^*[A].PreservesFlat]
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A vMap uMap (vMap ≫ uMap) rfl).hom.app
        (((derivedTensor A X).obj M).obj N) ≫
      (vMap)^*[A].leftDerivedFunctor.map
        ((leftDerivedUpperStarTensorIso A uMap M N).hom) ≫
      (leftDerivedUpperStarTensorIso A vMap
        ((uMap)^*[A].leftDerivedFunctor.obj M)
        ((uMap)^*[A].leftDerivedFunctor.obj N)).hom =
    (leftDerivedUpperStarTensorIso A (vMap ≫ uMap) M N).hom ≫
      ((leftDerivedUpperStarComp A vMap uMap (vMap ≫ uMap) rfl).hom.app M ⊗ₘ
        (leftDerivedUpperStarComp A vMap uMap (vMap ≫ uMap) rfl).hom.app N) := by
  simpa only [leftDerivedUpperStarTensorIso_hom, derivedTensor, curriedTensor_obj_obj,
    leftDerivedUpperStarDerivedTensor, Functor.postcompose₂_obj_obj_obj_obj, Functor.comp_obj] using
    (leftDerivedUpperStarTensorComparison_comp A vMap uMap (vMap ≫ uMap) rfl M N).symm

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Canonical derived étale inverse-image composition is monoidal.

(blueprint: lem-kun-derived-pullback-composition-monoidal)

Specialize the source library's tensor-composition and unit-composition coherence,
rewrite its tensor comparisons and unit comparisons as the canonical isomorphisms,
and use its left and right unitor equations. The final clause is the existing
componentwise associativity of the derived inverse-image composition isomorphism.
The tensor calculation is first made at a general coefficient category to keep the
monoidal instance in `derivedTensor` fixed before specializing to modules. -/
theorem canonicalDerivedPullbackCompositionMonoidal
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z T : Scheme.{u}}
    (uMap : Y ⟶ X) (vMap : Z ⟶ Y) (tMap : T ⟶ Z)
    (M N : DerivedCategoryModule Λ X) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≫
      (vMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) uMap M N).hom) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) vMap
        ((uMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj M)
        ((uMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj N)).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) (vMap ≫ uMap) M N).hom ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app M ⊗ₘ
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app N) ∧
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app
        (𝟙_ _) ≫
      (vMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) uMap).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) vMap).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (vMap ≫ uMap)).hom) ∧
    (∀ {V V' : Scheme.{u}} (w : V ⟶ V')
        (K : DerivedCategoryModule Λ V'),
      (w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) V' K).hom =
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) w (𝟙_ _) K).hom ≫
          ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) w).hom ⊗ₘ
            𝟙 ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K)) ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) V
            ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K)).hom) ∧
    (∀ {V V' : Scheme.{u}} (w : V ⟶ V')
        (K : DerivedCategoryModule Λ V'),
      (w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
          (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) V' K).hom =
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) w K (𝟙_ _)).hom ≫
          (𝟙 ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K) ⊗ₘ
            (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) w).hom) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) V
            ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K)).hom) ∧
    (∀ (K : DerivedCategoryModule Λ X),
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) tMap (vMap ≫ uMap)
          (tMap ≫ vMap ≫ uMap) (by simp)).hom.app K ≫
        (tMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap
            (vMap ≫ uMap) rfl).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (tMap ≫ vMap) uMap
          (tMap ≫ vMap ≫ uMap) (by simp)).hom.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) tMap vMap
          (tMap ≫ vMap) rfl).hom.app
          ((uMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K))
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact derivedPullbackCompositionTensor (ModuleCat.{u + 1} Λ) uMap vMap M N
  · have h := leftDerivedUpperStarComp_hom_app_unit
      (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl
    simpa only [leftDerivedUpperStarOplaxMonoidal_η] using h
  · intro V V' w K
    simpa only [leftDerivedUpperStarTensorIso_hom, tensorHom_id,
      derivedTensorLeftUnitor] using
      (leftDerivedUpperStarTensorComparison_leftUnitor_hom
        (ModuleCat.{u + 1} Λ) w K).symm
  · intro V V' w K
    simpa only [leftDerivedUpperStarTensorIso_hom, id_tensorHom,
      derivedTensorRightUnitor] using
      (leftDerivedUpperStarTensorComparison_rightUnitor_hom
        (ModuleCat.{u + 1} Λ) w K).symm
  · intro K
    exact leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} Λ)
      tMap vMap uMap (tMap ≫ vMap) (vMap ≫ uMap) (tMap ≫ vMap ≫ uMap)
      rfl rfl (by simp) K

end AlgebraicGeometry.Etale

end
