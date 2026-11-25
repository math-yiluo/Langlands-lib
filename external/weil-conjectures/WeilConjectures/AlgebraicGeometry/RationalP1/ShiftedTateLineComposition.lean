/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Ring.Int.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
import WeilConjectures.AlgebraicGeometry.RationalP1.DerivedCalculationInstances
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
/-! # Composition of shifted rational Tate-line comparisons

This is the composition calculation used by the rational
projective-line square, separated to keep individual file checking bounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local instance 30000] cachedModuleClosed
attribute [local instance 30000] CategoryTheory.sheafIsAbelian
attribute [local instance] CondensedRing.pullback_commShift
attribute [local irreducible] coefficient line
attribute [local irreducible] CondensedRing.upperStar Functor.leftDerivedFunctor
  Functor.singleFunctorCompLeftDerivedFunctorIso lineComparison
  CondensedRing.upperStarComp CondensedRing.leftDerivedUpperStarComp
  shiftedLineComparison
  DerivedCategory.singleFunctors Mod.monoidalClosed Mod.monoidalCategory
  Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

section ComparisonCalculations

attribute [local instance] CondensedRing.cachedFour CondensedRing.cachedGood12
  CondensedRing.cachedGood23 CondensedRing.cachedTensorLeft CondensedRing.cachedTensorRight
  CondensedRing.cachedSheafColimits CondensedRing.cachedSheafBigColimits
  CondensedRing.cachedCoequalizers CondensedRing.cachedModulePreadditive
  CondensedRing.cachedModuleFlatResolution CondensedRing.cachedExactSequential
  CondensedRing.cachedTensorLeftSequential CondensedRing.cachedTensorRightSequential

/-- Place the normalized underived comparison in degree zero. -/
@[irreducible] private def singleLineIso
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (moduleObjectDerivedPullback (coefficient l c).X f).obj
      ((DerivedCategory.singleFunctor (Modules (coefficient l c).X S) 0).obj (line l c S)) ≅
      (DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).obj (line l c X) :=
  (CondensedRing.upperStar (coefficient l c).X f).singleFunctorCompLeftDerivedFunctorIso.app
    (line l c S) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (lineComparison l c f)

private theorem single_line_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (CondensedRing.leftDerivedUpperStarComp (coefficient l c).X f g).hom.app
        ((DerivedCategory.singleFunctor (Modules (coefficient l c).X Z) 0).obj (line l c Z)) ≫
      (moduleObjectDerivedPullback (coefficient l c).X f).map (singleLineIso l c g).hom ≫
        (singleLineIso l c f).hom = (singleLineIso l c (f ≫ g)).hom := by
  unfold moduleObjectDerivedPullback
  simp only [singleLineIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    CondensedRing.leftDerivedUpperStarComp, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  have hn := (CondensedRing.upperStar (coefficient l c).X f).singleFunctorCompLeftDerivedFunctorIso
    |>.hom.naturality (lineComparison l c g).hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hc := Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj
    (CondensedRing.upperStar (coefficient l c).X g)
    (CondensedRing.upperStar (coefficient l c).X f) (line l c Z)
  rw [reassoc_of% hc]
  have he := Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj
    (CondensedRing.upperStar (coefficient l c).X (f ≫ g))
    (CondensedRing.upperStar (coefficient l c).X g ⋙
      CondensedRing.upperStar (coefficient l c).X f)
    (CondensedRing.upperStarComp (coefficient l c).X f g) (line l c Z)
  rw [reassoc_of% he]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun a : (CondensedRing.upperStar (coefficient l c).X (f ≫ g)).obj
        (line l c Z) ⟶ line l c X ↦
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar (coefficient l c).X (f ≫ g))).hom.app (line l c Z) ≫
          (DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).map a)
      (lineComparison_comp l c f g)

/-- The canonical comparison for a composite equals the two successive comparisons,
after the canonical derived compositor. Lift the prescribed underived composition
law by the degree-zero single functor and its exact comparison, then apply naturality
of the canonical shift comparison at shift 2. -/
theorem shifted_line_comparison_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (CondensedRing.leftDerivedUpperStarComp (coefficient l c).X f g).hom.app
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X Z) 0).obj
          (line l c Z)) ⟦(2 : ℤ)⟧) ≫
      (moduleObjectDerivedPullback (coefficient l c).X f).map
          (shiftedLineComparison l c g).hom ≫
        (shiftedLineComparison l c f).hom = (shiftedLineComparison l c (f ≫ g)).hom := by
  let := CondensedRing.pullbackComp_shift (coefficient l c).X f g
  simpa only [shiftedLineComparison, singleLineIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom] using
    shifted_composite_comparison (moduleObjectDerivedPullback (coefficient l c).X g)
      (moduleObjectDerivedPullback (coefficient l c).X f)
      (moduleObjectDerivedPullback (coefficient l c).X (f ≫ g))
      (CondensedRing.leftDerivedUpperStarComp (coefficient l c).X f g).hom _ _ _
      (singleLineIso l c g).hom (singleLineIso l c f).hom
      (singleLineIso l c (f ≫ g)).hom (single_line_comp l c f g) (2 : ℤ)

end ComparisonCalculations

end AlgebraicGeometry.ProEtale.RationalP1
