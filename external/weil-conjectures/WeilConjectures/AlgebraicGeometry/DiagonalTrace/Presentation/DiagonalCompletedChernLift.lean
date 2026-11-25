/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineComplete
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Lifting the Chern adjunct to completed coefficients

Source: blueprint latest, diagonal-tower trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private theorem complete_rightAdjoint
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R) (l : ℕ) (M : D)
    (hM : ∀ V : D, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M)) :
    ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ R.obj M) := by
  intro V hV
  have : IsIso (l • 𝟙 (L.obj V)) := by
    have he : L.map (l • 𝟙 V) = l • 𝟙 (L.obj V) :=
      (L.map_nsmul).trans (congrArg (fun a ↦ l • a) (L.map_id V))
    rw [← he]
    exact L.map_isIso (l • 𝟙 V)
  have := hM (L.obj V) inferInstance
  exact (adj.homEquiv V M).symm.injective.subsingleton

private theorem derives
    {A : Type*} [Category* A] [Abelian A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    (F : A ⥤ B) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{u + 1}) := by
  intro X Y f hf
  have hX : X.obj.IsKInjective := X.property
  have hY : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom))
  infer_instance

private def rightDerivedComparison
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F) :
    R.R ≅ F.rightDerivedFunctor := by
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let η : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    e.hom ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom
  have hi (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) := by
    dsimp [η]
    infer_instance
  have : F.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
    apply (derives F).isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    exact hi I.obj
  have := R.universal
  exact Functor.rightDerivedUnique _ _ R.η η
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- The Chern adjunct in strict constant-coefficient systems, before taking a limit.
Source: diagonal tower trace proof (1), restriction of the section class.
(blueprint: lem-diagonal-completed-chern-lift). -/
@[irreducible]
def Presentation.systemChern (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] {f : X ⟶ S}
    (p : Presentation l (ULift.{u} (Padic l)) f) :
    p.restrictionS.F.mapDerivedCategory.obj
        (unit S (Arings l (ULift.{u} (Padic l)) S)) ⟶
      p.Rt.R.obj (p.restrictionX.F.mapDerivedCategory.obj
        ((line l (ULift.{u} (Padic l)) p.chernX)⟦(2 : ℤ)⟧)) :=
  p.restrictionS.F.mapDerivedCategory.map
      (p.model.chernAdjoint l (ULift.{u} (Padic l))) ≫ p.varying.hom.app _

/-- Lift the system Chern adjunct using the full subcategory of complete objects.
Source: diagonal tower trace proof (1), and Stacks 099I and 099L.
(blueprint: lem-diagonal-completed-chern-lift).

Proof: the completed unit and the pushforward of the shifted completed Tate line
are derived complete. This is the same completeness argument as for the trace,
with the source and target interchanged. Fullness of completed scalar restriction
lifts the unit-limit comparison followed by Rlim of the system Chern adjunct and
the inverse pushforward/limit comparison. The latter is invertible by line_limit.
Cancel this comparison to obtain the stated normalization. The argument includes
the empty scheme. No trace equation or choice of an arbitrary finite lift is used. -/
theorem diagonalTrace_completedChern_lift
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃ c : completedUnit l S ⟶ p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧),
      (diagonalCompletedUnderlying l S).map c ≫
          p.sourceMap l (ULift.{u} (Padic l)) =
        p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
          p.LS.R.map (p.systemChern l) := by
  let F := diagonalCompletedUnderlying l S
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := diagonalCompleteScalarRestrictionCore l S
  let U := SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  have hunit := diagonalCompletedLine_complete l S U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  let inst : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule X l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} X l (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := diagonalCompletedLine_complete l X _ hfree
  let adjShift : shiftFunctor (DerivedCategory (DiagonalMod l X)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l X)) (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l X))
      (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint adjShift l
    ((diagonalCompletedUnderlying l X).obj (completedLine l X)) hline₀
  have hline : ∀ V : DerivedCategory (DiagonalMod l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l X).obj
        ((completedLine l X)⟦(2 : ℤ)⟧)) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      (((diagonalCompletedUnderlying l X).commShiftIso (2 : ℤ)).app
        (completedLine l X))
    constructor
    intro a b
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)
  let adj := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).mapDerivedCategoryRightDerivedAdjunction
  let e := rightDerivedComparison _ p.Rf
  have hpush := complete_rightAdjoint adj l
    ((diagonalCompletedUnderlying l X).obj ((completedLine l X)⟦(2 : ℤ)⟧)) hline
  have hsource : P (p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧)) := by
    intro V hV
    let c := (p.completed.iso.app ((completedLine l X)⟦(2 : ℤ)⟧)) ≪≫
      e.app ((diagonalCompletedUnderlying l X).obj ((completedLine l X)⟦(2 : ℤ)⟧))
    have := hpush V hV
    exact (Iso.homCongr (Iso.refl V) c).injective.subsingleton
  let A : P.FullSubcategory := ⟨_, hsource⟩
  let B : P.FullSubcategory := ⟨_, hunit⟩
  have := p.line_limit
  have hs : IsIso (p.sourceMap l (ULift.{u} (Padic l))) := by
    dsimp only [Presentation.sourceMap, shiftedComparison]
    infer_instance
  obtain ⟨c, hc⟩ := ff.map_surjective (X := B) (Y := A)
    (p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
      p.LS.R.map (p.systemChern l) ≫ inv (p.sourceMap l (ULift.{u} (Padic l))))
  change F.map c.hom = _ at hc
  refine ⟨c.hom, ?_⟩
  exact (congrArg (fun k ↦ k ≫ p.sourceMap l (ULift.{u} (Padic l))) hc).trans (by
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id])

end AlgebraicGeometry.ProEtale.DiagonalTrace
