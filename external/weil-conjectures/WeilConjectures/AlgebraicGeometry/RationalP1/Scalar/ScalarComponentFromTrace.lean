/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.ScalarTraceEquation
import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.AmbientTwistedUnitMate
import WeilConjectures.AlgebraicGeometry.RationalP1.ShiftedLineSquare

/-! # Twisted-unit compatibility from the scalar trace witness
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

set_option Elab.async false
attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
  condensedAmbientPullbackComparison
attribute [local irreducible] CondensedRing.upperStar Functor.leftDerivedFunctor
  Functor.singleFunctorCompLeftDerivedFunctorIso lineComparison
  CondensedRing.upperStarComp CondensedRing.leftDerivedUpperStarComp
  shiftedLineComparison secondLineComparison
  DerivedCategory.singleFunctors Mod.monoidalClosed Mod.monoidalCategory
  Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

-- Compare the fixed-endpoint wrapper before substituting the shifted line object.
private theorem secondPretraceExchangeMap_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    secondPretraceExchangeMap Λ Y M = (condensedAmbientExchange Λ (square Y)).app M := by
  unfold secondPretraceExchangeMap
  rfl

-- Apply the supplied trace equality without unfolding its geometric maps.
private theorem replace_right_factor
    {C : Type*} [Category C] {A B D : C} (a : A ⟶ B)
    {x y : B ⟶ D} {z : A ⟶ D} (h : x = y) (hm : a ≫ y = z) :
    a ≫ x = z :=
  (congrArg (fun b ↦ a ≫ b) h).trans hm

-- Substitute the middle arrow while keeping the concrete expression folded.
private theorem replace_middle_factor
    {C : Type*} [Category C] {A B D E : C} (a : A ⟶ B) (b : D ⟶ E)
    {x y : B ⟶ D} {z : A ⟶ E} (h : x = y) (hm : a ≫ y ≫ b = z) :
    a ≫ x ≫ b = z :=
  (congrArg (fun t ↦ a ≫ t ≫ b) h).trans hm

-- Specialize the geometric square before choosing the coefficient object or line.
private theorem selfSquare_twisted_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (A : DerivedCategory (Modules Λ Y))
    (B : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (Q : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj A ≅ B)
    (d : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj B ≅ Q)
    (e₂ : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj B ≅ Q)
    (h : (condensedAmbientPullbackComparison Λ (square Y)).hom.app A ≫
      (moduleObjectDerivedPullback Λ (firstProjection Y)).map e.hom ≫ d.hom =
      (moduleObjectDerivedPullback Λ (secondProjection Y)).map e.hom ≫ e₂.hom) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
        (scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) A B e) ≫
      secondPretraceExchangeMap Λ Y B ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map d.hom =
      e.hom ≫ scalarTwistedUnit Λ (secondProjection Y) B Q e₂ := by
  refine replace_middle_factor _ _ (secondPretraceExchangeMap_eq Λ Y B) ?_
  exact ambient_twisted_unit_mate Λ (square Y) e e.hom d.hom e₂ h

/-- Assemble the twisted-unit component from the explicit trace witness by
ambient mate naturality and the shifted line square. -/
theorem scalar_component_from_trace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (htrace : ScalarTraceWitness l c k p hpl Y) :
    let Λ := (coefficient l c).X
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map uq ≫ secondTraceExchange l c k p hpl Y =
        (scalarQLineIso l c k p hpl Y).hom ≫ u₂ := by
  dsimp only
  refine replace_right_factor _ htrace.exchange_eq ?_
  exact selfSquare_twisted_unit (coefficient l c).X Y _ _ _
    (scalarQLineIso l c k p hpl Y) (firstLineComparisonForTrace l c k p hpl Y)
    (secondLineComparison l c k p hpl Y) (shifted_line_square l c k p hpl Y)
end AlgebraicGeometry.ProEtale.RationalP1
