/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedSingleH0
@[expose] public noncomputable section
set_option autoImplicit false
universe u a v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
private theorem canonical_single
    {C D : Type a} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (R : DiagonalRightDerived F) (e : R.R = F.rightDerivedFunctor)
    (h : IsCanonicalRightDerived F R e) (M : C) :
    diagonalTraceRightSingle F R M ≫
        (eqToIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj M) =
      F.singleRightDerivedUnit.app M := by
  simp only [diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [R.R.map_id, Category.comp_id]
  rw [Category.assoc]
  erw [h]
  simp only [Functor.singleRightDerivedUnit_app, Functor.rightDerivedFunctorUnitQ,
    DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [Category.id_comp, F.rightDerivedFunctor.map_id, Category.comp_id]
  rfl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
/- Diagram-unit comparison for the single complex. -/
theorem projective_diagram_single (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    diagonalTraceRightSingle (CondensedRing.lowerStar Λ (secondProjection Y)) d.R₂
        (source Λ Y) ≫
      (secondDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) =
      (CondensedRing.lowerStar Λ (secondProjection Y)).singleRightDerivedUnit.app
        (source Λ Y) := by
  unfold secondDiagramPushIso
  exact canonical_single _ d.R₂ d.p₂_canonical d.p₂_unit (source Λ Y)
end AlgebraicGeometry.ProEtale.RationalP1
