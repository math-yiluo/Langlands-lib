/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonLimitIsos
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePushUnitSeed
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineComplete
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedRealizedUnitTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCanonicalUnitPush
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientOrdinarySquare
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerChernPullback
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived

/-! # Realized Chern classes of base Picard lines -/

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

private theorem complete_via_rightAdjoint
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
  let := hM (L.obj V) inferInstance
  exact (adj.homEquiv V M).symm.injective.subsingleton

private theorem baseChern_lift (l : ℕ) [Fact l.Prime]
    (S : Scheme.{u}) [IsNoetherian S] [DiagonalTraceLocalizations l S]
    (hS : IsUnit (l : Γ(S, ⊤)))
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) S)
    (r : DiagonalTrace.Restriction l (ULift.{u} (Padic l)) S)
    (a : DiagonalTrace.Coefficients l (ULift.{u} (Padic l)) S c r)
    (L : DiagonalRlim (DiagonalMod l S))
    (θ : SpTowerClasses.unit S (SpTowerClasses.Arings l (ULift.{u} (Padic l)) S) ⟶
      (SpTowerClasses.line l (ULift.{u} (Padic l)) c)⟦(2 : ℤ)⟧) :
    ∃! z : DiagonalTrace.completedUnit l S ⟶ (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧,
      (diagonalCompletedUnderlying l S).map z ≫
        DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l S)
          (r.F.mapDerivedCategory ⋙ L.R) (a.lineMap l (ULift.{u} (Padic l)) L) 2 =
        a.unitMap l (ULift.{u} (Padic l)) L ≫
          L.R.map (r.F.mapDerivedCategory.map θ) := by
  let F := diagonalCompletedUnderlying l S
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore l S
  let U := SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  have hunit := DiagonalTrace.diagonalCompletedLine_complete l S U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  let inst : ∀ x : S, Invertible (l : S.residueField x) := fun x ↦
    (show IsUnit (l : S.residueField x) from by
      let ψ := (S.residue x).hom.comp (S.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hS.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} S l (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := DiagonalTrace.diagonalCompletedLine_complete l S _ hfree
  let adj : shiftFunctor (DerivedCategory (DiagonalMod l S)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l S)) (2 : ℤ) :=
    (shiftEquiv' _ (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_via_rightAdjoint adj l
    (F.obj (DiagonalTrace.completedLine l S)) hline₀
  have hline : P ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      ((F.commShiftIso (2 : ℤ)).app (DiagonalTrace.completedLine l S))
    constructor
    intro b d
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e b) (e d)
  let A : P.FullSubcategory := ⟨_, hline⟩
  let B : P.FullSubcategory := ⟨_, hunit⟩
  let k := DiagonalTrace.shiftedComparison F (r.F.mapDerivedCategory ⋙ L.R)
    (a.lineMap l (ULift.{u} (Padic l)) L) 2
  have := DiagonalTrace.lineComparison_isIso l (ULift.{u} (Padic l)) a L
  have : IsIso k := by unfold k DiagonalTrace.shiftedComparison; infer_instance
  let b := a.unitMap l (ULift.{u} (Padic l)) L ≫ L.R.map (r.F.mapDerivedCategory.map θ)
  obtain ⟨z, hz⟩ := ff.map_surjective (X := B) (Y := A) (b ≫ inv k)
  change F.map z.hom = b ≫ inv k at hz
  refine ⟨z.hom, ?_, ?_⟩
  · change F.map z.hom ≫ k = b
    rw [hz, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro z' hz'
    change F.map z' ≫ k = b at hz'
    apply congrArg (fun q ↦ q.hom) (ff.map_injective (X := B) (Y := A) (f := ⟨z'⟩)
      (g := z) ?_)
    change F.map z' = F.map z.hom
    apply (cancel_mono k).mp
    rw [hz', hz, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem line_complete (l : ℕ) [Fact l.Prime]
    (S : Scheme.{u}) [IsNoetherian S] [DiagonalTraceLocalizations l S]
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧)) := by
  let inst : ∀ x : S, Invertible (l : S.residueField x) := fun x ↦
    (show IsUnit (l : S.residueField x) from by
      let ψ := (S.residue x).hom.comp (S.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hS.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} S l (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := DiagonalTrace.diagonalCompletedLine_complete l S _ hfree
  let adj : shiftFunctor (DerivedCategory (DiagonalMod l S)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l S)) (2 : ℤ) :=
    (shiftEquiv' _ (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_via_rightAdjoint adj l
    ((diagonalCompletedUnderlying l S).obj (DiagonalTrace.completedLine l S)) hline₀
  intro V hV
  let e := Iso.homCongr (Iso.refl V)
    (((diagonalCompletedUnderlying l S).commShiftIso (2 : ℤ)).app
      (DiagonalTrace.completedLine l S))
  constructor
  intro a b
  apply e.injective
  exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)

private theorem pushLine_complete (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hX : IsUnit (l : Γ(X, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        (p.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))) := by
  let adj := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).mapDerivedCategoryRightDerivedAdjunction
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  have := p.Rf.universal
  have := canonicalDiagonalUnit_universal G
  let e := Functor.rightDerivedUnique _ _ p.Rf.η (canonicalDiagonalUnit G)
    (HomologicalComplex.quasiIso (DiagonalMod l X) (.up ℤ))
  have hpush := complete_via_rightAdjoint adj l _ (line_complete l X hX)
  intro V hV
  let c := p.completed.iso.app ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) ≪≫
    e.app ((diagonalCompletedUnderlying l X).obj
      ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
  let := hpush V hV
  exact (Iso.homCongr (Iso.refl V) c).injective.subsingleton

-- Perform the factorization algebra with abstract objects and functors.
private theorem base_factor_map_calculation
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (L : E ⥤ D) {U V W : C} {A B T : E}
    (z : U ⟶ V) (b : V ⟶ W) (kS : F.obj V ⟶ L.obj B) (J : B ⟶ T)
    (kX : F.obj W ⟶ L.obj T) [IsIso kX] (u : F.obj U ⟶ L.obj A) (θ : A ⟶ B)
    (hb : F.map b = kS ≫ L.map J ≫ inv kX)
    (hz : F.map z ≫ kS = u ≫ L.map θ) :
    F.map (z ≫ b) ≫ kX = u ≫ L.map (θ ≫ J) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hz, Category.assoc]

private theorem limit_comparison_naturality
    {C0 C1 D0 D1 E0 E1 : Type*}
    [Category* C0] [Category* C1] [Category* D0] [Category* D1]
    [Category* E0] [Category* E1]
    (R : C0 ⥤ C1) (U : C0 ⥤ D0) (F : C1 ⥤ D1) (T : D0 ⥤ D1)
    (K : E0 ⥤ D0) (L : E1 ⥤ D1) (Q : E0 ⥤ E1)
    (σ : R ⋙ F ⟶ U ⋙ T) (τ : K ⋙ T ⟶ Q ⋙ L)
    {Z : C1} {X Y : C0} {X' Y' : E0}
    (b : Z ⟶ R.obj X) (w : X ⟶ Y) (k : U.obj Y ⟶ K.obj Y')
    (u : U.obj X ⟶ K.obj X') (θ : X' ⟶ Y')
    (hw : U.map w ≫ k = u ≫ K.map θ) :
    F.map (b ≫ R.map w) ≫ (σ.app Y ≫ T.map k ≫ τ.app Y') =
      (F.map b ≫ σ.app X ≫ T.map u ≫ τ.app X') ≫ L.map (Q.map θ) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (σ.naturality w)]
  rw [← T.map_comp_assoc, hw, T.map_comp]
  simp only [Category.assoc]
  have hτ := τ.naturality θ
  simp only [Functor.comp_map] at hτ
  rw [hτ]

private theorem map_naturality_postcomp
    {A B C D E : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (R : A ⥤ B) (U : B ⥤ D) (V : A ⥤ C) (T : C ⥤ D) (L : D ⥤ E)
    (σ : R ⋙ U ⟶ V ⋙ T) {X Y : A} {Z : B} {W : E}
    (a : Z ⟶ R.obj X) (f : X ⟶ Y) (u : W ⟶ L.obj (U.obj Z)) :
    (u ≫ L.map (U.map a ≫ σ.app X)) ≫ L.map (T.map (V.map f)) =
      u ≫ L.map (U.map (a ≫ R.map f) ≫ σ.app Y) := by
  have h := congrArg L.map (σ.naturality f)
  simp only [Functor.comp_map, Functor.map_comp] at h
  simp only [Functor.map_comp, Category.assoc]
  rw [← h]

private theorem base_factor_completed (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f) (M : S.Pic)
    (z : DiagonalTrace.completedUnit l S ⟶ (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧)
    (hz : (diagonalCompletedUnderlying l S).map z ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l S)
        (p.restrictionS.F.mapDerivedCategory ⋙ p.LS.R)
        (p.coefficientsS.lineMap l (ULift.{u} (Padic l)) p.LS) 2 =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map
          (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernS M)))
    (w : DiagonalTrace.completedUnit l X ⟶ (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (hw : (diagonalCompletedUnderlying l X).map w ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
        (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
        (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
      p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
        p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map
          (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX (Scheme.Pic.map f M)))) :
    ∃ b : (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧ ⟶
        p.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧),
      z ≫ b = ((DerivedCategory.singleFunctor _ 0).map
        (DiagonalTrace.completedPushUnit l f) ≫ singlePushComparison p.Rc _) ≫
          p.Rc.R.map w := by
  let E := ULift.{u} (Padic l)
  let F := diagonalCompletedUnderlying l S
  let θS := SpTowerClasses.firstChern l E p.chernS M
  let θX := SpTowerClasses.firstChern l E p.chernX (Scheme.Pic.map f M)
  let R := SpTowerShriek.push l E p.base p.model.geometry
  let P := SpTowerShriek.pull l E p.base p.model.geometry
  let adj := SpTowerShriek.adjunction l E p.base p.model.geometry
  let a := adj.homEquiv _ _ (p.model.coefficientPullback.derivedIso l E).hom
  let t := adj.homEquiv _ _ ((P.commShiftIso (2 : ℤ)).hom.app
    (SpTowerClasses.line l E p.chernS) ≫
      ((p.model.linePullback.derivedIso l E).hom)⟦(2 : ℤ)⟧')
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  let L := (fromSkeleton S.Modules).obj M.val
  let : Scheme.Modules.IsInvertible L := Scheme.Pic.isInvertible_fromSkeleton M
  have hL : Scheme.Pic.ofIsInvertible L = M := by
    apply Scheme.Pic.ext
    exact toSkeleton_fromSkeleton_obj M.val
  have hLf : Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) =
      Scheme.Pic.map f M := by rfl
  have hchern := tower_firstChern_pullback l E f hX hS p.base p.model.geometry
    p.chernS p.chernX p.normalizedS p.normalizedX
    p.model.coefficientPullback p.model.linePullback L
  rw [hL, hLf] at hchern
  have hc : a ≫ R.map θX = θS ≫ t := by
    calc
      _ = adj.homEquiv _ _ ((p.model.coefficientPullback.derivedIso l E).hom ≫ θX) :=
        (adj.homEquiv_naturality_right _ _).symm
      _ = _ := (congrArg (adj.homEquiv _ _) hchern.symm).trans
        (adj.homEquiv_naturality_left θS _)
  let kS := DiagonalTrace.shiftedComparison F (p.restrictionS.F.mapDerivedCategory ⋙ p.LS.R)
    (p.coefficientsS.lineMap l E p.LS) 2
  let J := p.restrictionS.F.mapDerivedCategory.map t ≫
    p.varying.hom.app ((SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧)
  let kX := p.sourceMap l E
  have := p.line_limit
  have : IsIso kX := by
    dsimp only [kX, DiagonalTrace.Presentation.sourceMap, DiagonalTrace.shiftedComparison]
    infer_instance
  let C : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun A ↦
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj A)
  obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore l S
  let A : C.FullSubcategory := ⟨_, line_complete l S hS⟩
  let B : C.FullSubcategory := ⟨_, pushLine_complete l f hX p⟩
  obtain ⟨b, hb⟩ := ff.map_surjective (X := A) (Y := B) (kS ≫ p.LS.R.map J ≫ inv kX)
  change F.map b.hom = kS ≫ p.LS.R.map J ≫ inv kX at hb
  let b₀ := (DerivedCategory.singleFunctor _ 0).map (DiagonalTrace.completedPushUnit l f) ≫
    singlePushComparison p.Rc _
  have hu : F.map b₀ ≫ p.completed.iso.hom.app (DiagonalTrace.completedUnit l X) ≫
      p.Rf.R.map (p.coefficientsX.unitMap l E p.LX) ≫ p.limits.iso.hom.app _ =
      p.coefficientsS.unitMap l E p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map a ≫ p.varying.hom.app _) := by
    have h := DiagonalTrace.diagonalTrace_finitePush_unit_seed l p
    simp only [DiagonalTrace.Presentation.finitePushUnit,
      diagonalTraceRightSingle, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp] at h
    erw [p.Rc.R.map_id, Category.comp_id] at h
    simpa only [a, b₀, singlePushComparison, Functor.map_comp, Category.assoc] using h
  refine ⟨b.hom, ?_⟩
  let U := SheafOfModules.unit
    (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  have hunit := DiagonalTrace.diagonalCompletedLine_complete l S U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  let UC : C.FullSubcategory := ⟨_, hunit⟩
  refine congrArg (fun k : UC ⟶ B ↦ k.hom) (ff.map_injective (X := UC) (Y := B)
    (f := ⟨z ≫ b.hom⟩) (g := ⟨b₀ ≫ p.Rc.R.map w⟩) ?_)
  change F.map (z ≫ b.hom) = F.map (b₀ ≫ p.Rc.R.map w)
  apply (cancel_mono kX).mp
  have hleft : F.map (z ≫ b.hom) ≫ kX =
      p.coefficientsS.unitMap l E p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map (θS ≫ t) ≫
          p.varying.hom.app _) := by
    simpa only [J, Functor.map_comp, Category.assoc] using
      base_factor_map_calculation F p.LS.R z b.hom kS J kX
        (p.coefficientsS.unitMap l E p.LS) (p.restrictionS.F.mapDerivedCategory.map θS) hb hz
  rw [hleft, ← hc]
  symm
  change F.map (b₀ ≫ p.Rc.R.map w) ≫
    (p.completed.iso.hom.app _ ≫ p.Rf.R.map _ ≫ p.limits.iso.hom.app _) = _
  rw [limit_comparison_naturality p.Rc.R (diagonalCompletedUnderlying l X) F
    p.Rf.R p.LX.R p.LS.R p.Rt.R p.completed.iso.hom p.limits.iso.hom
    b₀ w _ (p.coefficientsX.unitMap l E p.LX)
    (p.restrictionX.F.mapDerivedCategory.map θX) hw]
  rw [hu]
  exact map_naturality_postcomp R p.restrictionS.F.mapDerivedCategory
    p.restrictionX.F.mapDerivedCategory p.Rt.R p.LS.R p.varying.hom a θX
    (p.coefficientsS.unitMap l E p.LS)

private theorem realized_factor_calculation
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (H : C ⥤ E) (K : D ⥤ F) (R : D ⥤ C) (L : F ⥤ E)
    (σ : R ⋙ H ≅ K ⋙ L)
    {US LS : C} {UX LX : D} {U V : E} {W T : F}
    (su : H.obj US ⟶ U) [IsIso su] (sl : H.obj LS ⟶ V) [IsIso sl]
    (xu : K.obj UX ⟶ W) (xl : K.obj LX ⟶ T)
    (z : US ⟶ LS) (w : UX ⟶ LX) (b : LS ⟶ R.obj LX) (b₀ : US ⟶ R.obj UX)
    (q : W ⟶ T) (t : U ⟶ L.obj T)
    (hb : z ≫ b = b₀ ≫ R.map w)
    (hq : xu ≫ q = K.map w ≫ xl)
    (ht : H.map b₀ ≫ σ.hom.app UX ≫ L.map (xu ≫ q) = su ≫ t) :
    (inv su ≫ H.map z ≫ sl) ≫
      (inv sl ≫ H.map b ≫ σ.hom.app LX ≫ L.map xl) = t := by
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← H.map_comp_assoc, hb, H.map_comp]
  simp only [Category.assoc]
  have hp := σ.hom.naturality w
  simp only [Functor.comp_map] at hp
  rw [reassoc_of% hp]
  rw [← L.map_comp, ← hq, ht]
  simp only [IsIso.inv_hom_id_assoc]

private theorem adjunction_factor_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {U V B : C} {T : D} (i : B ≅ G.obj T)
    (q : F.obj U ⟶ T) (γ : U ⟶ V) (a : V ⟶ B)
    (h : γ ≫ a = adj.homEquiv U T q ≫ i.inv) :
    ∃ v : F.obj V ⟶ T, q = F.map γ ≫ v := by
  refine ⟨(adj.homEquiv V T).symm (a ≫ i.hom), ?_⟩
  apply (adj.homEquiv U T).injective
  rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  apply (cancel_mono i.inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

-- Isolate the concrete single-unit comparison from the diagram algebra.
private theorem localChern_unit (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (eX : CompletedRealization l X)
    (w : DiagonalTrace.completedUnit l X ⟶ (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) :
    eX.singleUnit l X ≫ eX.localChern l X w =
      eX.F.mapDerivedCategory.map w ≫ eX.shiftedLine l X := by
  have : IsIso (eX.singleUnit l X) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  unfold CompletedRealization.localChern
  simp only [IsIso.hom_inv_id_assoc]

-- Compare the two normalized unit transports with an arbitrary local target.
private theorem realized_unit_adjunct (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (push : CompletedPushSquare l f eX eS R D)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (T : DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
    (q : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶ T) :
    eS.F.mapDerivedCategory.map ((DerivedCategory.singleFunctor _ 0).map
      (DiagonalTrace.completedPushUnit l f) ≫ singlePushComparison R _) ≫
      push.derived.iso.hom.app (DiagonalTrace.completedUnit l X) ≫
        D.R.map (eX.singleUnit l X ≫ q) =
      eS.singleUnit l S ≫ modelLocalAdjunct
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f D canonical cF q := by
  exact (diagonalCompletedRealizedUnitTransport l f eX eS R D push T q).trans
    (congrArg (fun k ↦ eS.singleUnit l S ≫ k)
      (diagonalCanonicalUnitPush l f D canonical hcanonical cF T q))

private theorem modelAdjunct_factor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (canonical : D.R = derivedLower Λ f) (cF : UnitPullEndpoint Λ f)
    {T : DerivedCategory (Modules Λ X)} {V : DerivedCategory (Modules Λ S)}
    (q : unit Λ X ⟶ T) (γ : unit Λ S ⟶ V) (a : V ⟶ D.R.obj T)
    (h : γ ≫ a = modelLocalAdjunct Λ f D canonical cF q) :
    ∃ v : (derivedUpper Λ f).obj V ⟶ T,
      cF.derived ≫ q = (derivedUpper Λ f).map γ ≫ v := by
  let adj : derivedUpper Λ f ⊣ derivedLower Λ f :=
    CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
  apply adjunction_factor_of_iso adj ((eqToIso canonical).app T) (cF.derived ≫ q) γ a
  unfold modelLocalAdjunct at h
  exact h

private theorem modelAdjunct_factor_pair
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (canonical : D.R = derivedLower Λ f) (cF : UnitPullEndpoint Λ f)
    {T : DerivedCategory (Modules Λ X)} {V : DerivedCategory (Modules Λ S)}
    (q : unit Λ X ⟶ T) (γ : unit Λ S ⟶ V) (a : V ⟶ D.R.obj T)
    (h : γ ≫ a = modelLocalAdjunct Λ f D canonical cF q) :
    ∃ (γ' : unit Λ S ⟶ V) (v : (derivedUpper Λ f).obj V ⟶ T),
      cF.derived ≫ q = (derivedUpper Λ f).map γ' ≫ v := by
  exact ⟨γ, modelAdjunct_factor Λ f D canonical cF q γ a h⟩

-- Specialize coefficients while keeping the derived objects arbitrary.
private theorem concrete_factor_pair (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    {T : DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)}
    {V : DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)}
    (q : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶ T)
    (γ : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S ⟶ V)
    (a : V ⟶ D.R.obj T)
    (h : γ ≫ a = modelLocalAdjunct
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f D canonical cF q) :
    ∃ (γ' : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S ⟶ V)
      (v : (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).obj V ⟶ T),
      cF.derived ≫ q =
        (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map γ' ≫ v := by
  exact @modelAdjunct_factor_pair _ _ _ X S f D canonical cF T V q γ a h

-- Keep the realization diagram separate from the inverse-adjunction construction.
private theorem realized_factor_composite (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    [IsIso (eS.shiftedLine l S)]
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (push : CompletedPushSquare l f eX eS R D)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (z : DiagonalTrace.completedUnit l S ⟶ (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧)
    (w : DiagonalTrace.completedUnit l X ⟶ (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (b : (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧ ⟶
      R.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (hb : z ≫ b = ((DerivedCategory.singleFunctor _ 0).map
      (DiagonalTrace.completedPushUnit l f) ≫ singlePushComparison R _) ≫ R.R.map w) :
    eS.localChern l S z ≫ (inv (eS.shiftedLine l S) ≫
      eS.F.mapDerivedCategory.map b ≫ push.derived.iso.hom.app _ ≫
        D.R.map (eX.shiftedLine l X)) =
      modelLocalAdjunct (Profinite.continuousMapRingObj.{u} ℤ_[l]) f D canonical cF
        (eX.localChern l X w) := by
  have : IsIso (eS.singleUnit l S) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  have : IsIso (eS.shiftedLine l S) := by
    unfold CompletedRealization.shiftedLine
    infer_instance
  conv_lhs =>
    lhs
    unfold CompletedRealization.localChern
  exact realized_factor_calculation eS.F.mapDerivedCategory eX.F.mapDerivedCategory
    R.R D.R push.derived.iso (eS.singleUnit l S) (eS.shiftedLine l S)
    (eX.singleUnit l X) (eX.shiftedLine l X) z w b _
    (eX.localChern l X w) _ hb (localChern_unit l X eX w)
    (realized_unit_adjunct l f eX eS R D canonical hcanonical push cF _
      (eX.localChern l X w))

-- The concrete specialization compares derived sheaf and coefficient instances.
private theorem realize_factorization (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (push : CompletedPushSquare l f eX eS R D)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (z : DiagonalTrace.completedUnit l S ⟶ (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧)
    (w : DiagonalTrace.completedUnit l X ⟶ (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (b : (DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧ ⟶
      R.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (hb : z ≫ b = ((DerivedCategory.singleFunctor _ 0).map
      (DiagonalTrace.completedPushUnit l f) ≫ singlePushComparison R _) ≫ R.R.map w) :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let V := ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj
      (zlLine l S))⟦(2 : ℤ)⟧
    let T := ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj
      (zlLine l X))⟦(2 : ℤ)⟧
    ∃ (γ : unit Λ S ⟶ V) (v : (derivedUpper Λ f).obj V ⟶ T),
      cF.derived ≫ eX.localChern l X w = (derivedUpper Λ f).map γ ≫ v := by
  have : IsIso (eS.shiftedLine l S) := by
    unfold CompletedRealization.shiftedLine
    infer_instance
  exact concrete_factor_pair l f D canonical cF (eX.localChern l X w) (eS.localChern l S z) _
    (realized_factor_composite l f eX eS R D canonical hcanonical push cF z w b hb)

/-- A realized local Chern class of a base line factors through the shifted
integral Tate line on that base, before taking any right adjunct.

Source: diagonal coefficient changes (3), base Chern component of the Picard decomposition.
(blueprint: lem-diagonal-local-chern-base-factorization).

Proof: represent M by an invertible module L. Whole-system Chern naturality
for L, read through the tower pullback/push adjunction, gives a;R(θ_X)=θ_S;t,
where a is the adjunct of the coefficient-unit pullback and t that of the
shifted line pullback. The completed unit and the shifted integral root line on
S are complete (local freeness of rank one, shift adjunction), and so is
p.Rc(completedLine_X[2]) (p.completed, uniqueness of right-derived functors and
the pullback/direct-image adjunction). Full faithfulness of scalar restriction
on complete objects lifts the base normalization of θ_S to z on S, and lifts
the restricted, derived-limit image of t (conjugated by the line comparisons
and p.sourceMap) to b with z;b=b₀;p.Rc(w), where b₀ is the completed push unit;
this uses the finite-push unit seed, naturality of p.completed, p.limits and
p.varying, and hw. Choose a completed realization e_S on S, the canonical
condensed right-derived direct image D and the derived ordinary realization
square. Put γ=localChern_S(z) and realize b as a:V→D(T). The realized-unit
transport and canonical-unit-push theorems identify γ;a with the derived
adjunct of cF.derived;localChern_X(w); v is the inverse adjunct of a, and
naturality of the derived adjunction gives the factorization. The direct-image
data are constructed inside the proof; the statement uses no horizontal square,
no hyperplane summand, no trace, and no direct-image or exchange comparison. -/
theorem diagonalLocalChern_base_factorization (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hunit : IsUnit (l : Γ(S, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (eX : CompletedRealization l X)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (M : S.Pic)
    (w : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧)
    (hw : (diagonalCompletedUnderlying l X).map w ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
        (p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R)
        (p.coefficientsX.lineMap l (ULift.{u} (Padic l)) p.LX) 2 =
      p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX ≫
        p.LX.R.map (p.restrictionX.F.mapDerivedCategory.map
          (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
            (Scheme.Pic.map f M)))) :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let V := ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj
      (zlLine l S))⟦(2 : ℤ)⟧
    let T := ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj
      (zlLine l X))⟦(2 : ℤ)⟧
    ∃ (γ : unit Λ S ⟶ V) (v : (derivedUpper Λ f).obj V ⟶ T),
      cF.derived ≫ eX.localChern l X w = (derivedUpper Λ f).map γ ≫ v := by
  -- Construct the existential line factor by adjunction; its normalization follows
  -- from the whole-system Chern equation and the completed coefficient-unit seed.
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
  obtain ⟨z, hz, _⟩ := baseChern_lift l S hunit p.chernS p.restrictionS
    p.coefficientsS p.LS (SpTowerClasses.firstChern l _ p.chernS M)
  obtain ⟨b, hb⟩ := base_factor_completed l f hunit p M z hz w hw
  obtain ⟨eS⟩ := completedCoefficientRealization_exists l S hunit
  let D := canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f)
  have canonical : D.R = derivedLower Λ f := rfl
  have hcanonical : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) D canonical := by
    intro K
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  obtain ⟨ordinary⟩ := completedCoefficientOrdinarySquare_exists l f eX eS
  let push : CompletedPushSquare l f eX eS p.Rc D := ordinary.derive
  exact realize_factorization l f eX eS p.Rc D canonical hcanonical push cF z w b hb

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
