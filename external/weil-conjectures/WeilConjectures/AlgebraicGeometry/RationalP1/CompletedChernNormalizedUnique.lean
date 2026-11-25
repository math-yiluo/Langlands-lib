/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineCompleteAux
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift

/-! Uniqueness of the normalized completed Chern adjunct. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing DiagonalTrace Opposite

-- A degree-zero coefficient module is complete as soon as its sequence difference is
-- invertible. Countable exact products on the pro-etale site allow the single functor
-- to preserve this difference and its product.
private theorem complete_of_difference
    (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) [DiagonalTraceLocalizations l S]
    (L : DiagonalCompleted l S)
    (hL : IsIso ((sequenceDifference (DiagonalMod l S) l).app
      ((diagonalCompletedRestriction l S).obj L))) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj L)) := by
  have : PreservesLimitsOfShape (Discrete ℕ)
      ((CochainComplex.singleFunctors (DiagonalMod l S)).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _
      (HomologicalComplex.single (DiagonalMod l S) (.up ℤ) 0))
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor (DiagonalMod l S) 0) :=
    preservesLimitsOfShape_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (DiagonalMod l S) 0).symm
  let e := ((diagonalCompletedRestriction l S).mapDerivedCategorySingleFunctor 0).app L
  intro V hV
  have := hV
  have h := sequenceDifference_orthogonal
    (DerivedCategory.singleFunctor (DiagonalMod l S) 0) l
    ((diagonalCompletedRestriction l S).obj L) hL V
  exact ⟨fun f g ↦ (cancel_mono e.hom).mp (h.elim (f ≫ e.hom) (g ≫ e.hom))⟩

-- Restricting scalars leaves the same additive sheaf, so the difference may be
-- checked after forgetting all scalar actions.
private theorem difference_of_underlying
    (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) (L : DiagonalCompleted l S)
    (hL : IsIso ((sequenceDifference (DiagonalAb S) l).app
      ((diagonalForget l S).obj ((diagonalCompletedRestriction l S).obj L)))) :
    IsIso ((sequenceDifference (DiagonalMod l S) l).app
      ((diagonalCompletedRestriction l S).obj L)) := by
  let F := diagonalForget l S
  let M := (diagonalCompletedRestriction l S).obj L
  have : PreservesLimitsOfShape (Discrete ℕ) F :=
    (diagonalScalarAdjunction l S).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : F.ReflectsIsomorphisms := by
    change (sheafCompose (Scheme.ProEt.topology S)
      (ModuleCat.restrictScalars.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[l])) ⋙
          forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).ReflectsIsomorphisms
    infer_instance
  have : IsIso (F.map ((sequenceDifference (DiagonalMod l S) l).app M)) :=
    (sequenceDifference_map_isIso_iff F l M).mpr hL
  exact isIso_of_reflects_iso _ F

private theorem completed_unit_complete
    (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) [DiagonalTraceLocalizations l S] :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj (completedUnit l S)) := by
  apply complete_of_difference
  apply difference_of_underlying
  exact completedCoefficient_difference l S

-- The completed Tate line is the ordinary limit of the actual finite root sheaves.
-- Each level is killed by l^(n+1), so its sequence difference has a finite geometric
-- series inverse. Sequence products commute with this limit.
private theorem completed_line_complete
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [DiagonalTraceLocalizations l X] :
    ∀ V : DerivedCategory (DiagonalMod l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l X).obj (completedLine l X)) := by
  apply complete_of_difference
  apply difference_of_underlying
  change IsIso ((sequenceDifference (DiagonalAb X) l).app
    (limit (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime))))
  apply sequenceDifference_limit
  intro n
  apply sequenceDifference_nilpotent l _ (n.unop + 1)
  ext U x
  exact Scheme.proEtaleRootsOfUnity_nsmul X (l ^ (n.unop + 1)) U x

/-- A normalized completed Chern adjunct is unique. -/
theorem completedChernNormalized_unique
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S}
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (a a' : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l p a)
    (ha' : CompletedChernNormalized l p a') : a = a' := by
  let F := diagonalCompletedUnderlying l S
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := diagonalCompleteScalarRestrictionCore l S
  have hline₀ := completed_line_complete l X
  let adjShift : shiftFunctor (DerivedCategory (DiagonalMod l X)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l X)) (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l X))
      (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint adjShift l
    ((diagonalCompletedUnderlying l X).obj (completedLine l X)) hline₀
  have hline : ∀ V : DerivedCategory (DiagonalMod l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l X).obj
        ((completedLine l X) ⟦(2 : ℤ)⟧)) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      (((diagonalCompletedUnderlying l X).commShiftIso (2 : ℤ)).app (completedLine l X))
    constructor
    intro b c
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e b) (e c)
  let adj := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).mapDerivedCategoryRightDerivedAdjunction
  let e := rightDerivedComparison _ p.Rf
  have hpush := complete_rightAdjoint adj l
    ((diagonalCompletedUnderlying l X).obj ((completedLine l X) ⟦(2 : ℤ)⟧)) hline
  have htarget : P (p.Rc.R.obj ((completedLine l X) ⟦(2 : ℤ)⟧)) := by
    intro V hV
    let c := (p.completed.iso.app ((completedLine l X) ⟦(2 : ℤ)⟧)) ≪≫
      e.app ((diagonalCompletedUnderlying l X).obj ((completedLine l X) ⟦(2 : ℤ)⟧))
    have := hpush V hV
    exact (Iso.homCongr (Iso.refl V) c).injective.subsingleton
  let A : P.FullSubcategory := ⟨_, completed_unit_complete l S⟩
  let B : P.FullSubcategory := ⟨_, htarget⟩
  have := p.line_limit
  have : IsIso (p.sourceMap l (ULift.{u} (Padic l))) := by
    dsimp only [Presentation.sourceMap, shiftedComparison]
    infer_instance
  have hab : F.map a = F.map a' :=
    (cancel_mono (p.sourceMap l (ULift.{u} (Padic l)))).mp (ha.trans ha'.symm)
  have h : (ObjectProperty.homMk a : A ⟶ B) = ObjectProperty.homMk a' :=
    ff.map_injective hab
  exact congrArg (fun b : A ⟶ B ↦ b.hom) h

end AlgebraicGeometry.ProEtale.RationalP1
