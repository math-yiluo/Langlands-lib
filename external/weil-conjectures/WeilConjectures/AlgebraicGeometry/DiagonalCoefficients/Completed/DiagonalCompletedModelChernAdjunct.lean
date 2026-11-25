/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePushUnitSeed
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineComplete
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedRealizedUnitTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCanonicalUnitPush

/-! # Realization of a normalized local Chern adjunct -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar
  CompletedRealization.singleUnit CompletedRealization.shiftedLine

private theorem complete_rightAdjoint'
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

private theorem derives'
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

private def rightDerivedComparison'
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F) :
    R.R ≅ F.rightDerivedFunctor := by
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      π ⋙ H :=
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
    apply (derives' F).isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    exact hi I.obj
  have := R.universal
  exact Functor.rightDerivedUnique _ _ R.η η
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

private theorem completed_map_injective'
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (a b : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (h : (diagonalCompletedUnderlying l S).map a =
      (diagonalCompletedUnderlying l S).map b) : a = b := by
  let F := diagonalCompletedUnderlying l S
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore l S
  let U := SheafOfModules.unit
    (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  have hunit := DiagonalTrace.diagonalCompletedLine_complete l S U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  let inst : ∀ x : X, Invertible (l : X.residueField x) :=
    fun x ↦ (show IsUnit (l : X.residueField x) from by
      let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule X l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} X l
      (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := DiagonalTrace.diagonalCompletedLine_complete l X _ hfree
  let adjShift : shiftFunctor (DerivedCategory (DiagonalMod l X))
      (-2 : ℤ) ⊣ shiftFunctor (DerivedCategory (DiagonalMod l X))
      (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l X))
      (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint' adjShift l
    ((diagonalCompletedUnderlying l X).obj
      (DiagonalTrace.completedLine l X)) hline₀
  have hline : ∀ V : DerivedCategory (DiagonalMod l X),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶
        (diagonalCompletedUnderlying l X).obj
          ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      (((diagonalCompletedUnderlying l X).commShiftIso (2 : ℤ)).app
        (DiagonalTrace.completedLine l X))
    constructor
    intro a b
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)
  let adj := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
      f).mapDerivedCategoryRightDerivedAdjunction
  let e := rightDerivedComparison' _ p.Rf
  have := p.line_limit
  have hpush := complete_rightAdjoint' adj l
    ((diagonalCompletedUnderlying l X).obj
      ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)) hline
  have hsource : P (p.Rc.R.obj
      ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)) := by
    intro V hV
    let c := (p.completed.iso.app
      ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)) ≪≫
        e.app ((diagonalCompletedUnderlying l X).obj
          ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    have := hpush V hV
    exact (Iso.homCongr (Iso.refl V) c).injective.subsingleton
  exact congrArg (fun k ↦ k.hom) (ff.map_injective (X := ⟨_, hunit⟩)
    (Y := ⟨_, hsource⟩) (show (P.ι ⋙ F).map ⟨a⟩ = (P.ι ⋙ F).map ⟨b⟩ from h))

-- The complete-object and comparison calculations use concrete localization instances.
/-- Realization identifies a completed Chern adjunct with the canonical derived
adjunct of its normalized local Chern class.

Source: diagonal trace proof (1), and coefficient changes (1), the first adjunct square.
(blueprint: lem-diagonal-completed-model-chern-adjunct).

Proof: expand the model Chern adjunct as the adjunction unit followed by the
pushforward of its actual hyperplane class. Restrict this equation to the whole
constant-coefficient system. The coefficient-unit seed and naturality of the
varying and limit comparisons show that the completed adjunct of z has exactly
the normalization of b. Both source and target are complete, so full faithfulness
of completed scalar restriction identifies those completed maps. Apply the exact
realization and its universally normalized push square. Its ordinary unit
normalization and the full canonical derived-unit equation identify the realized
unit with the canonical condensed adjunction unit. Naturality moves the realized
local arrow through the push square; cancel the specified unit and line isomorphisms.
No Cartesian square or trace identity is used here. -/
theorem diagonalCompletedModelChern_adjunct (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (push : CompletedPushSquare l f eX eS p.Rc D)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (b : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (hb : RationalP1.CompletedChernNormalized l p b)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (hz : ModelLocalChernNormalized l p z) :
    RationalP1.realizeScalarChern l f eX eS p.Rc D push b =
      modelLocalAdjunct _ f D canonical cF (eX.localChern l X z) := by
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
  let UX := SheafOfModules.unit
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  let m := DiagonalTrace.completedPushUnit l f
  let b₀ := (DerivedCategory.singleFunctor _ 0).map m ≫
    singlePushComparison p.Rc UX
  let theta := SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
    (Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S))
  let unitSys := p.restrictionS.F.mapDerivedCategory.map
      (SpTowerClasses.unitArrow l (ULift.{u} (Padic l)) p.model.coefficientPullback) ≫
        p.varying.hom.app _
  have hsystem : p.systemChern l = unitSys ≫
      p.Rt.R.map (p.restrictionX.F.mapDerivedCategory.map theta) := by
    have hmodel : p.model.chernAdjoint l (ULift.{u} (Padic l)) =
        SpTowerClasses.unitArrow l (ULift.{u} (Padic l)) p.model.coefficientPullback ≫
          (SpTowerShriek.push l (ULift.{u} (Padic l)) p.base p.model.geometry).map theta := by
      unfold DiagonalTrace.Model.chernAdjoint
      rw [Adjunction.homEquiv_unit]
      dsimp only [theta]
      unfold SpTowerClasses.unitArrow
      rw [Scheme.Pic.mapHom_apply]
      simp only [Functor.map_comp, Category.assoc]
    unfold DiagonalTrace.Presentation.systemChern
    rw [hmodel, Functor.map_comp]
    have hn := p.varying.hom.naturality theta
    have hh := congrArg (fun k ↦ p.restrictionS.F.mapDerivedCategory.map
        (SpTowerClasses.unitArrow l (ULift.{u} (Padic l)) p.model.coefficientPullback) ≫ k) hn
    simp only [unitSys, Functor.comp_map, Category.assoc] at hh ⊢
    convert! hh using 1
  have hu : (diagonalCompletedUnderlying l S).map b₀ ≫
      p.completed.iso.hom.app (DiagonalTrace.completedUnit l X) ≫
      p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX) ≫
        p.limits.iso.hom.app _ =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map unitSys := by
    have h := DiagonalTrace.diagonalTrace_finitePush_unit_seed l p
    simp only [DiagonalTrace.Presentation.finitePushUnit,
      diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp] at h
    erw [p.Rc.R.map_id, Category.comp_id] at h
    simpa only [unitSys, SpTowerClasses.unitArrow, Adjunction.homEquiv_unit,
      Functor.map_comp, Category.assoc, b₀, m, singlePushComparison] using h
  have hbc : b = b₀ ≫ p.Rc.R.map z := by
    apply completed_map_injective' l f hS p
    have : IsIso (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) :=
      p.line_limit
    have hsource : IsIso (p.sourceMap l (ULift.{u} (Padic l))) := by
      dsimp only [DiagonalTrace.Presentation.sourceMap, DiagonalTrace.shiftedComparison]
      infer_instance
    have := hsource
    apply (cancel_mono (p.sourceMap l (ULift.{u} (Padic l)))).mp
    have hl := hz
    unfold ModelLocalChernNormalized at hl
    have hcn := hb
    unfold RationalP1.CompletedChernNormalized at hcn
    change (diagonalCompletedUnderlying l X).map z ≫
        DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
          (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
          (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
      p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
        p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map theta) at hl
    change (diagonalCompletedUnderlying l S).map b ≫
        p.sourceMap l (ULift.{u} (Padic l)) =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map (p.systemChern l) at hcn
    rw [hcn, hsystem]
    symm
    dsimp only [DiagonalTrace.Presentation.sourceMap]
    simp only [Functor.map_comp, Category.assoc]
    have hn := p.completed.iso.hom.naturality z
    have hlim := p.limits.iso.hom.naturality
      (p.restrictionX.F.mapDerivedCategory.map theta)
    erw [reassoc_of% hn]
    erw [← p.Rf.R.map_comp_assoc, hl, p.Rf.R.map_comp]
    simp only [Category.assoc]
    erw [hlim]
    simpa only [Category.assoc, Functor.comp_map] using
      congrArg (fun k ↦ k ≫ p.LS.R.map
        (p.Rt.R.map (p.restrictionX.F.mapDerivedCategory.map theta))) hu
  have : IsIso (eX.singleUnit l X) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  have : IsIso (eS.singleUnit l S) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  have hlocal : eX.singleUnit l X ≫ eX.localChern l X z =
      eX.F.mapDerivedCategory.map z ≫ eX.shiftedLine l X := by
    unfold CompletedRealization.localChern
    simp only [IsIso.hom_inv_id_assoc]
  have htransport := diagonalCompletedRealizedUnitTransport l f eX eS p.Rc D push _
    (eX.localChern l X z)
  have hcanon := diagonalCanonicalUnitPush l f D canonical hcanonical cF _
    (eX.localChern l X z)
  have hp : eS.F.mapDerivedCategory.map (p.Rc.R.map z) ≫
      push.derived.iso.hom.app _ =
      push.derived.iso.hom.app _ ≫ D.R.map (eX.F.mapDerivedCategory.map z) := by
    exact push.derived.iso.hom.naturality z
  unfold RationalP1.realizeScalarChern
  rw [hbc, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hp]
  rw [← D.R.map_comp, ← hlocal]
  erw [htransport]
  simp only [IsIso.inv_hom_id_assoc]
  exact hcanon

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
