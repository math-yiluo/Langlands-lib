/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerAdjunctConditions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedRealizedUnitTransport
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePushUnitSeed
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineComplete
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # The completed first square for a normalized Chern adjunct

Source: diagonal tower coefficient changes (1), passage from the canonical model to
completed coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a v w wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint derivedScalars RestrictionSquare.mate
  CompletedRealization.singleUnit CompletedRealization.shiftedLine
  FiniteRealization.derivedUnit

section SingleSquare
variable {A B C D : Type a}
  [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
  {F : A ⥤ B} {G : C ⥤ D} [F.Additive] [G.Additive]
  (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
  (ordinary : F ⋙ V ≅ U ⋙ G)

private theorem singleFactor (M : A) :
    (U.mapDerivedCategorySingleFunctor 0).hom.app M =
      U.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) := by
  exact (Iso.inv_comp_eq (U.mapDerivedCategoryFactors.app _)).mp
    (U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M)

/-- The full derived-unit square evaluated on a single coefficient object.
Source: diagonal trace universal-unit normalization.
(blueprint: def-diagonal-coefficient-unit-push).
Proof: evaluate the normalization on the single complex and cancel the canonical
single-complex comparisons. Their coherence is checked in each degree. -/
private theorem single_square
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary) (M : A) :
    V.mapDerivedCategory.map (singlePushComparison RF M) ≫
        s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) ≫
          singlePushComparison RG (U.obj M) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  have hn := s.normalization P
  unfold singlePushComparison
  rw [singleFactor U M, RG.R.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  have hη := RG.η.naturality
    ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)
  change DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)) ≫
      RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M)) =
    RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫ RG.R.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)) at hη
  erw [← hη]
  have hV := V.mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  change V.mapDerivedCategory.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    V.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫
      DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) at hV
  erw [reassoc_of% hV]
  rw [singleFactor V (F.obj M)]
  have hc :
      (V.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) =
      (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (F.obj M) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (ordinary.hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (U.obj M) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f]
      dsimp [P, HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
      change V.map (𝟙 (F.obj M)) ≫ ordinary.hom.app M ≫
        G.map (𝟙 (U.obj M)) =
          (𝟙 (V.obj (F.obj M))) ≫
            ((𝟙 (V.obj (F.obj M))) ≫ ordinary.hom.app M ≫ (𝟙 _)) ≫ (𝟙 _)
      simp only [Category.id_comp, Category.comp_id]
      exact (congrArg₂ (fun k h => k ≫ ordinary.hom.app M ≫ h)
        (V.map_id (F.obj M)) (G.map_id (U.obj M))).trans
          ((Category.id_comp _).trans (Category.comp_id _))
    · simp [P, HomologicalComplex.singleMapHomologicalComplex,
        HomologicalComplex.single, hn]
  have hs : (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single D (.up ℤ) 0).map (ordinary.hom.app M)) := rfl
  rw [hs]
  have hq := congrArg DerivedCategory.Q.map hc
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k => V.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫ k ≫
        RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))) hq

end SingleSquare

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

private theorem completed_map_injective
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y)
    (a b : DiagonalTrace.completedUnit l Y ⟶
      s.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    (h : (diagonalCompletedUnderlying l Y).map a =
      (diagonalCompletedUnderlying l Y).map b) : a = b := by
  let F := diagonalCompletedUnderlying l Y
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l Y)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l Y),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore l Y
  let U := SheafOfModules.unit (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))
  have hunit := DiagonalTrace.diagonalCompletedLine_complete l Y U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    apply (isUnit_pow_iff (Nat.succ_ne_zero s.n)).mp
    simpa only [Nat.cast_pow] using s.hYpow
  have hX : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  let inst : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (show IsUnit (l : (ProjectiveLine Y).residueField x) from by
      let ψ := ((ProjectiveLine Y).residue x).hom.comp
        ((ProjectiveLine Y).presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule (ProjectiveLine Y) l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} (ProjectiveLine Y) l
      (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := DiagonalTrace.diagonalCompletedLine_complete l (ProjectiveLine Y) _ hfree
  let adjShift : shiftFunctor (DerivedCategory (DiagonalMod l (ProjectiveLine Y)))
      (-2 : ℤ) ⊣ shiftFunctor (DerivedCategory (DiagonalMod l (ProjectiveLine Y))) (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l (ProjectiveLine Y)))
      (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint adjShift l
    ((diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
      (DiagonalTrace.completedLine l (ProjectiveLine Y))) hline₀
  have hline : ∀ V : DerivedCategory (DiagonalMod l (ProjectiveLine Y)),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶
        (diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
          ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      (((diagonalCompletedUnderlying l (ProjectiveLine Y)).commShiftIso (2 : ℤ)).app
        (DiagonalTrace.completedLine l (ProjectiveLine Y)))
    constructor
    intro a b
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)
  let adj := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
      (ProjectiveLine Y ↘ Y)).mapDerivedCategoryRightDerivedAdjunction
  let e := rightDerivedComparison _ s.tq.Rf
  have hpush := complete_rightAdjoint adj l
    ((diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
      ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)) hline
  have hsource : P (s.tq.Rc.R.obj
      ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)) := by
    intro V hV
    let c := (s.tq.completed.iso.app
      ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)) ≪≫
        e.app ((diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
          ((DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    have := hpush V hV
    exact (Iso.homCongr (Iso.refl V) c).injective.subsingleton
  exact congrArg (fun k => k.hom) (ff.map_injective (X := ⟨_, hunit⟩)
    (Y := ⟨_, hsource⟩) (show (P.ι ⋙ F).map ⟨a⟩ = (P.ι ⋙ F).map ⟨b⟩ from h))

-- Transport a normalized unit square before specializing the derived categories.
private theorem adjunct_transport_calculation
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (U : A ⥤ C) (V : B ⥤ D) (S : C ⥤ D)
    (σ : R ⋙ V ⟶ U ⋙ S) {US : B} {UX LX : A} {US' : D} {UX' LX' : C}
    (i : U.obj UX ≅ UX') (u : V.obj US ⟶ US') (a : US' ⟶ S.obj UX')
    (b : US ⟶ R.obj UX) (z : UX ⟶ LX) (k : U.obj LX ⟶ LX')
    (h : V.map b ≫ σ.app UX ≫ S.map i.hom = u ≫ a) :
    V.map (b ≫ R.map z) ≫ (σ.app LX ≫ S.map k) =
      u ≫ (a ≫ S.map ((i.inv ≫ U.map z) ≫ k)) := by
  have hb : V.map b ≫ σ.app UX = u ≫ a ≫ S.map i.inv := by
    apply (cancel_mono (S.map i.hom)).mp
    simpa only [Category.assoc, ← S.map_comp, i.inv_hom_id,
      S.map_id, Category.comp_id] using h
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (σ.naturality z), ← Category.assoc, hb]
  simp only [Category.assoc]

private theorem map_comp_naturality_square
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ⥤ B) (U : B ⥤ C) (V : A ⥤ D) (T : D ⥤ C)
    (σ : R ⋙ U ⟶ V ⋙ T) {X Y : A} {Z : B} (a : Z ⟶ R.obj X) (f : X ⟶ Y) :
    U.map (a ≫ R.map f) ≫ σ.app Y =
      (U.map a ≫ σ.app X) ≫ T.map (V.map f) := by
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ U.map a ≫ k) (σ.naturality f)

/-- Realizing the normalized completed adjunct gives the condensed adjunct of the local arrow.
Source: diagonal tower coefficient changes (1), and diagonal tower trace proof (1).
(blueprint: lem-diagonal-completed-adjunct-square).

Proof: the model identity makes its Picard pullback O(1). The coefficient-one
normalization identifies the coefficient pullback unit with the canonical unit.
The varying ordinary section equation and full derived-unit normalization transport
model.chernAdjoint to the strict constant-coefficient system. Naturality of the
constant-system/limit adjunction and the limit-square normalization show that the
completed adjunct of z has exactly the sourceMap equation defining c. Restriction
on complete objects is fully faithful; the unit, shifted root line and its direct
image are complete, so that equation identifies the two completed arrows. Finally
apply the normalized completed realization square and its ordinary unit equation.
Only this first realization is involved: there is no integral extension, quotient,
finite realization, finite Kummer class or trace identity in this conclusion. The
argument also applies on the empty scheme. -/
theorem completed_adjunct_square
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y) (p : NormalizedAdjunctPair l Y s) :
    let uP := (s.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso s.completedP.unitIso
    s.completedY.F.mapDerivedCategory.map p.c ≫
        (s.q_square.derived.iso.hom.app _ ≫
          s.zl.Rq.R.map (s.completedP.shiftedLine l (ProjectiveLine Y))) =
      s.completedY.singleUnit l Y ≫
        (coefficientUnitPush _ Y s.zl.Rq ≫ s.zl.Rq.R.map
          ((uP.inv ≫ s.completedP.F.mapDerivedCategory.map p.z) ≫
            s.completedP.shiftedLine l (ProjectiveLine Y))) := by
  let t := s.tq.toPresentation
  let UY := SheafOfModules.unit (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))
  let UP := SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
    (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))
  let G := CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l])
    (ProjectiveLine Y ↘ Y)
  let m := DiagonalTrace.completedPushUnit l (ProjectiveLine Y ↘ Y)
  have hm : s.completedY.F.map m ≫ s.q_square.ordinary.hom.app UP ≫
      G.map s.completedP.unitIso.hom =
    s.completedY.unitIso.hom ≫ coefficientOrdinaryUnit _ Y :=
    completed_ordinary_unit l Y s.completedY s.completedP
      s.q_square.ordinary s.q_square.ordinary_normalization
  let b := (DerivedCategory.singleFunctor _ 0).map m ≫ singlePushComparison t.Rc UP
  let iP := (s.completedP.F.mapDerivedCategorySingleFunctor 0).app UP ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso s.completedP.unitIso
  have hb : s.completedY.F.mapDerivedCategory.map b ≫
      s.q_square.derived.iso.hom.app (DiagonalTrace.completedUnit l (ProjectiveLine Y)) ≫
        s.zl.Rq.R.map iP.hom =
    s.completedY.singleUnit l Y ≫ coefficientUnitPush _ Y s.zl.Rq := by
    unfold CompletedRealization.singleUnit coefficientUnitPush
    exact realization_unit_square s.completedP.F s.completedY.F t.Rc s.zl.Rq
      s.q_square.ordinary s.q_square.derived UP UY _ _
      s.completedP.unitIso s.completedY.unitIso m (coefficientOrdinaryUnit _ Y) hm
  let theta := SpTowerClasses.firstChern l (ULift.{u} (Padic l)) t.chernX
    (SpTowerClasses.hyperplanePic Y)
  let unitSys := t.restrictionS.F.mapDerivedCategory.map
      (SpTowerClasses.unitArrow l (ULift.{u} (Padic l)) t.model.coefficientPullback) ≫
        t.varying.hom.app _
  have hsystem : t.systemChern l = unitSys ≫
      t.Rt.R.map (t.restrictionX.F.mapDerivedCategory.map theta) := by
    have hmodel : t.model.chernAdjoint l (ULift.{u} (Padic l)) =
        SpTowerClasses.unitArrow l (ULift.{u} (Padic l)) t.model.coefficientPullback ≫
          (SpTowerShriek.push l (ULift.{u} (Padic l)) t.base t.model.geometry).map theta := by
      unfold DiagonalTrace.Model.chernAdjoint
      have hp : Scheme.Pic.mapHom t.model.model.hom (SpTowerClasses.hyperplanePic Y) =
          SpTowerClasses.hyperplanePic Y := by
        rw [show t.model.model = Iso.refl (ProjectiveLine Y) from s.q_model]
        exact Scheme.Pic.map_id _
      rw [hp, Adjunction.homEquiv_unit, Functor.map_comp]
      simp only [SpTowerClasses.unitArrow, theta, Category.assoc]
    unfold DiagonalTrace.Presentation.systemChern
    rw [hmodel]
    exact map_comp_naturality_square _ _ _ _ t.varying.hom _ theta
  have hu : (diagonalCompletedUnderlying l Y).map b ≫
    t.completed.iso.hom.app (DiagonalTrace.completedUnit l (ProjectiveLine Y)) ≫
      t.Rf.R.map (t.coefficientsX.unitMap l (ULift.{u} (Padic l)) t.LX) ≫
        t.limits.iso.hom.app _ = t.coefficientsS.unitMap l (ULift.{u} (Padic l)) t.LS ≫
          t.LS.R.map unitSys := by
    have h := DiagonalTrace.diagonalTrace_finitePush_unit_seed l t
    simp only [DiagonalTrace.Presentation.finitePushUnit,
      diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp] at h
    erw [t.Rc.R.map_id, Category.comp_id] at h
    simpa only [unitSys, SpTowerClasses.unitArrow, Adjunction.homEquiv_unit,
      Functor.map_comp, Category.assoc, b, m, singlePushComparison] using h
  have hc : p.c = b ≫ t.Rc.R.map p.z := by
    apply completed_map_injective l Y s
    have := t.line_limit
    have : IsIso (t.sourceMap l (ULift.{u} (Padic l))) := by
      dsimp only [DiagonalTrace.Presentation.sourceMap, DiagonalTrace.shiftedComparison]
      infer_instance
    apply (cancel_mono (t.sourceMap l (ULift.{u} (Padic l)))).mp
    have hl := p.local_normalized
    unfold UniformizerChernNormalizationData.LocalNormalized at hl
    change (diagonalCompletedUnderlying l (ProjectiveLine Y)).map p.z ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l (ProjectiveLine Y))
        (t.restrictionX.F.mapDerivedCategory ⋙ t.LX.R)
        (t.coefficientsX.lineMap l (ULift.{u} (Padic l)) t.LX) 2 =
      t.coefficientsX.unitMap l (ULift.{u} (Padic l)) t.LX ≫
        t.LX.R.map (t.restrictionX.F.mapDerivedCategory.map theta) at hl
    have hn := t.completed.iso.hom.naturality p.z
    have hlim := t.limits.iso.hom.naturality
      (t.restrictionX.F.mapDerivedCategory.map theta)
    have hcn := p.adjunct_normalized
    unfold UniformizerChernNormalizationData.AdjunctNormalized at hcn
    change (diagonalCompletedUnderlying l Y).map p.c ≫ t.sourceMap l (ULift.{u} (Padic l)) =
      t.coefficientsS.unitMap l (ULift.{u} (Padic l)) t.LS ≫ t.LS.R.map (t.systemChern l) at hcn
    rw [hcn, hsystem]
    symm
    dsimp only [DiagonalTrace.Presentation.sourceMap]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hn]
    erw [← t.Rf.R.map_comp_assoc, hl, t.Rf.R.map_comp]
    simp only [Category.assoc]
    erw [hlim]
    simpa only [Category.assoc, Functor.comp_map] using
      congrArg (fun k ↦ k ≫ t.LS.R.map
        (t.Rt.R.map (t.restrictionX.F.mapDerivedCategory.map theta))) hu
  change s.completedY.F.mapDerivedCategory.map p.c ≫
      (s.q_square.derived.iso.hom.app _ ≫
        s.zl.Rq.R.map (s.completedP.shiftedLine l (ProjectiveLine Y))) =
    s.completedY.singleUnit l Y ≫
      (coefficientUnitPush _ Y s.zl.Rq ≫ s.zl.Rq.R.map
        ((iP.inv ≫ s.completedP.F.mapDerivedCategory.map p.z) ≫
          s.completedP.shiftedLine l (ProjectiveLine Y)))
  rw [hc]
  exact adjunct_transport_calculation t.Rc.R s.completedP.F.mapDerivedCategory
    s.completedY.F.mapDerivedCategory s.zl.Rq.R s.q_square.derived.iso.hom
    iP (s.completedY.singleUnit l Y) (coefficientUnitPush _ Y s.zl.Rq)
    b p.z (s.completedP.shiftedLine l (ProjectiveLine Y)) hb

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
