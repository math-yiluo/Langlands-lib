/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorPullback
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimPullbackEndpoints
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTensorGeometryExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassLinePullbackExistence

/-! # Normalized scalar squares for whole-tower Chern pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u a v w r
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace SpTowerClasses

-- Keep module inverse-image constructions folded while elaborating the data record.
attribute [local irreducible] Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleDirectImage Scheme.proEtaleRingModuleAdjunction
  upperStar lowerStar diagonalCompletedRestriction diagonalCompletedCoefficientMap

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

private def LimitAdjunctionNormalized
    (A : Type a) [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A)
    (adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R) : Prop :=
  (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory.map (L.η.app I) ≫
        adj.counit.app (DerivedCategory.Q.obj I) =
      (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ) constLimAdj).counit.app I)) ∧
  (∀ (n : ℕ) (K : DerivedCategory (ℕᵒᵖ ⥤ A)),
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map (adj.counit.app K) =
      (ringedConstantTowerEvaluation A (op n)).hom.app (L.R.obj K) ≫
        (L.projection n).app K)

private theorem limitAdjunctionNormalized_exists
    (A : Type a) [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] (L : DiagonalRlim A) :
    ∃ adj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⊣ L.R,
      LimitAdjunctionNormalized A L adj := by
  let := L.universal
  have huniv (G : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A) :
      Function.Bijective (fun β : L.R ⟶ G ↦ L.η ≫ Functor.whiskerLeft DerivedCategory.Q β) := by
    constructor
    · intro α β h
      exact Functor.rightDerived_ext _ L.η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) G α β h
    · intro β
      exact ⟨Functor.rightDerivedDesc _ L.η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) G β,
        Functor.rightDerived_fac _ L.η _ G β⟩
  obtain ⟨adj, c, π, hc, hcounit, hresolution, hprojection, _⟩ :=
    derived_tower_counit_projections.{a, v, w, w, 0, 0} A
      (fun K ↦ by
        obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
        exact ⟨I, q, hI, hq⟩) L.R L.η huniv L.computation
  have hc_eq (n : ℕ) : c n = ringedConstantTowerEvaluation A (op n) := by
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    exact (hc n K).trans (CategoryTheory.rct_eval_fac A (op n) K)
  have hπ_eq (n : ℕ) : π n = L.projection n := by
    apply NatTrans.ext
    funext K
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    let : IsIso (L.η.app I) := L.computation I hI
    have hIπ : (π n).app (DerivedCategory.Q.obj I) =
        (L.projection n).app (DerivedCategory.Q.obj I) := by
      apply (cancel_epi (L.η.app I)).mp
      apply (cancel_mono
        (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I)).mp
      have h := hresolution n I I (𝟙 I) hI
      have h' : L.η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app I =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
        have hf : L.R.map (DerivedCategory.Q.map (𝟙 I)) = 𝟙 _ :=
          (congrArg (fun q ↦ L.R.map q) (DerivedCategory.Q.map_id I)).trans
            (L.R.map_id _)
        have hi : inv (L.R.map (DerivedCategory.Q.map (𝟙 I))) = 𝟙 _ := by
          apply (cancel_mono (L.R.map (DerivedCategory.Q.map (𝟙 I)))).mp
          exact (IsIso.inv_hom_id _).trans
            (hf.symm.trans (Category.id_comp _).symm)
        have he : DerivedCategory.Q.map
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map
              (𝟙 I)) = 𝟙 _ :=
          (congrArg (fun q ↦ DerivedCategory.Q.map q)
            ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).map_id I)).trans
              (DerivedCategory.Q.map_id _)
        rw [hi, he] at h
        erw [Category.id_comp, Category.comp_id] at h
        exact h
      simpa only [Category.assoc] using h'.trans (L.normalization I n).symm
    apply (cancel_mono
      (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map e.hom)).mp
    rw [← (π n).naturality e.hom, ← (L.projection n).naturality e.hom, hIπ]
  refine ⟨adj, hcounit, ?_⟩
  intro n K
  simpa only [hc_eq, hπ_eq] using hprojection n K

private lemma tower_grothendieck
    (A : Type a) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{r} A] :
    IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{r, r} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

-- The counit normalization in the exact form of the hypotheses of
-- `diagonalRlim_pullback_endpoints`, whose cochain complexes carry the fixed-coefficient zero
-- morphisms. Proving it once, for an arbitrary scheme, keeps that instance comparison out of the
-- main theorem, where it would be paid for both schemes.
private theorem counit_normalized (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (L : DiagonalRlim (DiagonalMod l X))
    (adj : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ ℕᵒᵖ ⥤ DiagonalMod l X).mapDerivedCategory ⊣
      L.R)
    (h : LimitAdjunctionNormalized (DiagonalMod l X) L adj) :
    ∀ (I : CochainComplex (ℕᵒᵖ ⥤ DiagonalMod l X) ℤ), I.IsKInjective →
      (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ ℕᵒᵖ ⥤ DiagonalMod l X).mapDerivedCategory.map
          (L.η.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤
          ℕᵒᵖ ⥤ DiagonalMod l X).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ DiagonalMod l X) ⥤ DiagonalMod l X).mapHomologicalComplex (.up ℤ)).obj
            I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplex (.up ℤ)
            (constLimAdj : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ ℕᵒᵖ ⥤ DiagonalMod l X) ⊣
              lim)).counit.app I) :=
  h.1

/-- Normalization of an exact pullback mate on every ordinary tower cone.
Source: blueprint coefficient changes (3)
(blueprint: lem-diagonal-local-chern-pullback-data). -/
def LocalChernConeMate
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (P : A ⥤ B) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj P)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj P)]
    (L : DiagonalRlim A) (L' : DiagonalRlim B)
    (β : L.R ⋙ P.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj P).mapDerivedCategory ⋙ L'.R) : Prop :=
  ∀ (K : ℕᵒᵖ ⥤ A) (c : Cone K),
    P.mapDerivedCategory.map (diagonalTraceConeMap L K c) ≫
        β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj K) ≫
        L'.R.map
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj P).mapDerivedCategorySingleFunctor
              0).hom.app K) =
      (P.mapDerivedCategorySingleFunctor 0).hom.app c.pt ≫
        diagonalTraceConeMap L' (((Functor.whiskeringRight ℕᵒᵖ A B).obj P).obj K)
          (P.mapCone c)

-- The record retains two scalar squares and their complete derived cone equations.
/-- Ordinary scalar squares and a natural comparison for the entire derived tower.

Source: latest blueprint, diagonal coefficient changes (3), pullback of the normalized
coefficient and root cones (blueprint: lem-diagonal-local-chern-pullback-data).
The cone equation is an equality before evaluation at any finite level. -/
structure LocalChernPullbackData (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f') where
  base : SpTowerShriek.Base l (ULift.{u} (Padic l))
  geometry : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) base hX
  coefficient : CoefficientPullback l (ULift.{u} (Padic l)) base hX geometry
  line : LinePullback l (ULift.{u} (Padic l)) hX geometry p.chernX p'.chernX
  completedOrdinary :
    diagonalCompletedRestriction l X ⋙ (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX) ≅
      diagonalRealizationPull l hX ⋙ diagonalCompletedRestriction l X'
  completedPush : Scheme.proEtaleRingModuleDirectImage hX
      (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
      (asIso (diagonalCompletedCoefficientMap l hX)) ⋙ diagonalCompletedRestriction l X ≅
    diagonalCompletedRestriction l X' ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX
  completedPush_sections : ∀ (M : DiagonalCompleted l X') (U : X.ProEtᵒᵖ)
      (x : ((Scheme.proEtaleRingModuleDirectImage hX
        (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
        (asIso (diagonalCompletedCoefficientMap l hX)) ⋙
        diagonalCompletedRestriction l X).obj M).obj.obj U),
    HEq ((completedPush.hom.app M).hom.app U x) x
  completedMate :
    (mateEquiv (Scheme.proEtaleRingModuleAdjunction hX
        (Scheme.purTwistZlCompletion X l) (Scheme.purTwistZlCompletion X' l)
        (asIso (diagonalCompletedCoefficientMap l hX)))
      (upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)
      (TwoSquare.mk _ _ _ _ completedOrdinary.hom)) = completedPush.hom
  varyingOrdinary : p.restrictionX.F ⋙ ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X)
      (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)) ≅
    geometry.pull ⋙ p'.restrictionX.F
  varyingPush : geometry.push ⋙ p.restrictionX.F ≅
    p'.restrictionX.F ⋙ diagonalTraceSystemPush l hX
  varyingPush_sections : ∀ (M : Systems X' (Arings l (ULift.{u} (Padic l)) X'))
      (n : ℕ) (U : X.ProEtᵒᵖ)
      (x : (((geometry.push ⋙ p.restrictionX.F).obj M).obj (op n)).obj.obj U),
    HEq (((varyingPush.hom.app M).app (op n)).hom.app U x) x
  varyingMate :
    (mateEquiv geometry.ordinaryAdjunction
      ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).whiskerRight ℕᵒᵖ)
      (TwoSquare.mk _ _ _ _ varyingOrdinary.hom)) = varyingPush.hom
  [towerLimits : PreservesFiniteLimits (((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X)
      (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)))]
  [towerColimits : PreservesFiniteColimits (((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X)
      (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)))]
  limitMate : p.LX.R ⋙ ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
      hX)).mapDerivedCategory ⟶
    (((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX))).mapDerivedCategory ⋙ p'.LX.R
  mateShifts : NatTrans.CommShift limitMate ℤ
  cone : LocalChernConeMate
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX) p.LX p'.LX limitMate

/-- The natural comparison on the entire varying derived system.
Source: blueprint coefficient changes (3)
(blueprint: lem-diagonal-local-chern-pullback-data). -/
def LocalChernPullbackData.comparison (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {hX : X' ⟶ X}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    {p : Presentation l (ULift.{u} (Padic l)) f}
    {p' : Presentation l (ULift.{u} (Padic l)) f'}
    (d : LocalChernPullbackData l hX p p') :
    ((p.restrictionX.F.mapDerivedCategory ⋙ p.LX.R) ⋙
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory) ⟶
    SpTowerShriek.pull l (ULift.{u} (Padic l)) d.base d.geometry ⋙
      p'.restrictionX.F.mapDerivedCategory ⋙ p'.LX.R := by
  letI := d.geometry.pullAdditive
  letI := d.geometry.pullLimits
  letI := d.geometry.pullColimits
  letI := p.restrictionX.additive
  letI := p.restrictionX.limits
  letI := p.restrictionX.colimits
  letI := p'.restrictionX.additive
  letI := p'.restrictionX.limits
  letI := p'.restrictionX.colimits
  letI := d.towerLimits
  letI := d.towerColimits
  exact (Functor.associator p.restrictionX.F.mapDerivedCategory p.LX.R
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX).mapDerivedCategory).hom ≫
    Functor.whiskerLeft p.restrictionX.F.mapDerivedCategory d.limitMate ≫
    (Functor.associator p.restrictionX.F.mapDerivedCategory
      ((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l X')).obj
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) hX)).mapDerivedCategory p'.LX.R).inv ≫
    Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d.varyingOrdinary).hom p'.LX.R ≫
    (Functor.associator (SpTowerShriek.pull l (ULift.{u} (Padic l)) d.base d.geometry)
      p'.restrictionX.F.mapDerivedCategory p'.LX.R).hom

/-- The exact completed scalar square of the pullback data.
Source: blueprint coefficient changes (3)
(blueprint: lem-diagonal-local-chern-pullback-data). -/
abbrev LocalChernPullbackData.completedSquare (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {hX : X' ⟶ X}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    {p : Presentation l (ULift.{u} (Padic l)) f}
    {p' : Presentation l (ULift.{u} (Padic l)) f'}
    (d : LocalChernPullbackData l hX p p') :=
  Functor.mapDerivedCategorySquareIso d.completedOrdinary

-- Instantiate the normalized endpoint theorem with both independent presentations.
/-- Normalized scalar pullback squares and the whole derived-limit mate exist.

Source: latest blueprint, diagonal coefficient changes (3).
(blueprint: lem-diagonal-local-chern-pullback-data).

Proof: choose the coefficient-unit-normalized tensor geometry, then its normalized
positive-root line. Use the constant-tower/limit adjunction determined by the full
cochain counit. The derived tower counit theorem and the specified projection
normalization identify all its projections. Apply diagonalRlim_pullback_endpoints.
Its varying and completed scalar squares provide the two ordinary squares, their
section normalizations and mate equations. Its natural limit mate, shift law and
full ordinary cone equation supply the remaining fields. -/
theorem diagonalLocalChern_pullback_data (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} (hX : X' ⟶ X)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (p' : Presentation l (ULift.{u} (Padic l)) f')
    (hunit : IsUnit (l : Γ(X, ⊤))) :
    Nonempty (LocalChernPullbackData l hX p p') := by
  obtain ⟨b, g, ⟨q⟩, ⟨k⟩⟩ := exists_tensorGeometry l (ULift.{u} (Padic l)) hX
  obtain ⟨t⟩ := linePullback_nonempty l (ULift.{u} (Padic l)) hX g q k hunit
    p.chernX p'.chernX p.normalizedX p'.normalizedX
  let : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
    tower_grothendieck (DiagonalMod l X)
  let : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X') :=
    tower_grothendieck (DiagonalMod l X')
  obtain ⟨adj, hc, hp⟩ := limitAdjunctionNormalized_exists (DiagonalMod l X) p.LX
  obtain ⟨adj', hc', hp'⟩ := limitAdjunctionNormalized_exists (DiagonalMod l X') p'.LX
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hunit.map ψ).invertible
  have hunit' : IsUnit (l : Γ(X', ⊤)) := by
    simpa only [map_natCast] using hunit.map hX.appTop.hom
  let : ∀ x : X', Invertible (l : X'.residueField x) := fun x ↦
    (show IsUnit (l : X'.residueField x) from by
      let ψ := (X'.residue x).hom.comp (X'.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hunit'.map ψ).invertible
  obtain ⟨_, _, _, hcone, _, _, hV, hC, hshift, _⟩ :=
    diagonalRlim_pullback_endpoints l hX p'.LX p.LX adj' adj
      (counit_normalized l X' p'.LX adj' ⟨hc', hp'⟩) hp'
      (counit_normalized l X p.LX adj ⟨hc, hp⟩) hp
      p.chernX p.restrictionX p.coefficientsX
  obtain ⟨dV, vV, ndV, mV, _⟩ := hV b g p'.restrictionX
  obtain ⟨dC, vC, ndC, mC, _⟩ := hC
  let W := diagonalRlimTowerPull l hX
  let : PreservesFiniteLimits W :=
    { preservesFiniteLimits := fun _ _ _ ↦ by
        dsimp only [W, diagonalRlimTowerPull]
        infer_instance }
  let : PreservesFiniteColimits W :=
    { preservesFiniteColimits := fun _ _ _ ↦ by
        dsimp only [W, diagonalRlimTowerPull]
        infer_instance }
  have hc : LocalChernConeMate (diagonalRlimPull l hX) p.LX p'.LX
      (diagonalRlimPullbackMate l hX p'.LX p.LX adj' adj) := by
    intro H c
    exact hcone H c
  exact ⟨{
    base := b
    geometry := g
    coefficient := q
    line := t
    completedOrdinary := vC
    completedPush := dC
    completedPush_sections := ndC
    completedMate := mC
    varyingOrdinary := vV
    varyingPush := dV
    varyingPush_sections := ndV
    varyingMate := mV
    towerLimits := inferInstanceAs (PreservesFiniteLimits W)
    towerColimits := inferInstanceAs (PreservesFiniteColimits W)
    limitMate := diagonalRlimPullbackMate l hX p'.LX p.LX adj' adj
    mateShifts := hshift
    cone := hc }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
