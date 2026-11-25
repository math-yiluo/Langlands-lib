/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceScalarComparisons
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The actual finite direct-image operation for the diagonal trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory diagonalTracePush

/-- Evaluation commutes with ordinary direct image of constant-scalar towers.
Source: diagonal tower limit proof (1), levelwise direct image.
(blueprint: def-sfb-diagonal-trace-finite-evaluation). -/
def finiteEvaluationOrdinary (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) :
    diagonalTraceSystemPush l f ⋙ (evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n) ≅
      (evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n) ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f := Iso.refl _

/-- The unit-normalized exact square for evaluation and total direct image.
Its normalization determines its isomorphism uniquely.
Source: diagonal tower limit proof (1), evaluation preserves K-injectives because
its left adjoint is exact; uniqueness of total right derived functors.
(blueprint: def-sfb-diagonal-trace-finite-evaluation). -/
@[no_expose] def finiteEvaluationSquare (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S)
    (Rt : DiagonalRightDerived (diagonalTraceSystemPush l f))
    (Rf : DiagonalRightDerived
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)) (n : ℕ) :
    ExactSquare (diagonalTraceSystemPush l f)
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
      ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n))
      ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n))
      Rt Rf (finiteEvaluationOrdinary l f n) := by
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod l X)
  let e := squareOfAcyclic (diagonalTraceSystemPush l f)
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n))
    ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n))
    Rt Rf (finiteEvaluationOrdinary l f n) (by
      intro I hI
      have := hI
      exact Rf.computation _ (tower_evaluation_isKInjective (DiagonalMod l X) I (op n)))
  exact ⟨e.iso, e.normalization⟩

/-- The completed coefficient unit into the ordinary completed direct image.
Source: diagonal tower trace proof (2), the unital coefficient map for f.
(blueprint: def-sfb-diagonal-trace-finite-evaluation). -/
def completedPushUnit (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S) :
    let MS : DiagonalCompleted l S :=
      SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
    let MX : DiagonalCompleted l X :=
      SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    MS ⟶ (diagonalTracePush l f).obj MX := by
  let unitToPushforwardRestrictedUnit
      {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      {F : C ⥤ D} [F.IsContinuous J K]
      {R : Sheaf J RingCat.{u + 1}} {S T : Sheaf K RingCat.{u + 1}}
      (α : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S) (φ : S ⟶ T) :
      SheafOfModules.unit.{u, u + 1, u + 1} R ⟶
        (SheafOfModules.pushforward.{u + 1} α).obj
          ((SheafOfModules.restrictScalars φ).obj (SheafOfModules.unit T)) :=
    SheafOfModules.unitToPushforwardObjUnit
      (α ≫ (F.sheafPushforwardContinuous RingCat J K).map φ)
  unfold diagonalTracePush Scheme.proEtaleRingedDirectImage
  exact unitToPushforwardRestrictedUnit
    (C := S.ProEt) (D := X.ProEt)
    (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology X)
    (F := Scheme.proEtaleBaseChange f)
    (R := Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
    (S := Scheme.proEtaleModuleCoefficients
      ((Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (Scheme.purTwistZlCompletion S l)))
    (T := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    ⟨Functor.whiskerRight
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app
        (Scheme.purTwistZlCompletion S l)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap l f))

/-- The actual completed coefficient unit, restricted to constant scalars.
Source: diagonal tower trace proof (2), before evaluation.
(blueprint: def-sfb-diagonal-trace-finite-evaluation). -/
def Presentation.finitePushUnit (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    (diagonalCompletedUnderlying l S).obj (completedUnit l S) ⟶
      p.Rf.R.obj ((diagonalCompletedUnderlying l X).obj (completedUnit l X)) :=
  (diagonalCompletedUnderlying l S).map
      ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).map
          (completedPushUnit l f) ≫
        diagonalTraceRightSingle (diagonalTracePush l f) p.Rc _) ≫
    p.completed.iso.hom.app _

/-- Evaluation/direct image followed by the inverse varying-scalar comparison.
Source: diagonal tower trace proof (2), evaluation of the common direct image.
(blueprint: def-sfb-diagonal-trace-finite-evaluation). -/
def Presentation.finitePushComparison (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) (n : ℕ) :
    (p.restrictionX.F.mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n)).mapDerivedCategory) ⋙ p.Rf.R ≅
      SpTowerShriek.push l (ULift.{u} (Padic l)) p.base p.model.geometry ⋙
        (p.restrictionS.F.mapDerivedCategory ⋙
          ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft p.restrictionX.F.mapDerivedCategory
      (finiteEvaluationSquare l f p.Rt p.Rf n).iso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight p.varying.symm _ ≪≫ Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.DiagonalTrace
