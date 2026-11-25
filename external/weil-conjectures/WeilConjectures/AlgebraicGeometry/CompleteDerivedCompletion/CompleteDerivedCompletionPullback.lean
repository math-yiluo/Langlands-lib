/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletionDefs
public import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Towers and the derived completion: pullback and pushforward

Levelwise pullback of towers is exact and commutes with evaluation; the mates of the
evaluation interchanges are isomorphisms compatible with units, counits and transitions.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory.UnboundedExactTower

section General

/-- Mates are compatible with whiskering the two vertical sides of a square.
Source: blueprint Assertion 3, transition compatibility
(blueprint: proposition-proper-base-change-complete-integral).
Proof: expand the mate as unit, square and counit; move the left whiskering through the
unit by naturality, apply the hypothesis, and move the right whiskering past the counit. -/
theorem mateEquiv_whisker_app
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ H} {R₂ : H ⥤ E}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) {G G' : C ⥤ E} {K K' : D ⥤ H}
    (α : TwoSquare G L₁ L₂ K) (α' : TwoSquare G' L₁ L₂ K') (s : G' ⟶ G) (t : K' ⟶ K)
    (h : ∀ X : C, L₂.map (s.app X) ≫ α.app X = α'.app X ≫ t.app (L₁.obj X)) (Y : D) :
    s.app (R₁.obj Y) ≫ (mateEquiv a b α).app Y =
      (mateEquiv a b α').app Y ≫ R₂.map (t.app Y) := by
  have e1 {G₀ : C ⥤ E} {K₀ : D ⥤ H} (α₀ : TwoSquare G₀ L₁ L₂ K₀) :
      (mateEquiv a b α₀).app Y = b.unit.app (G₀.obj (R₁.obj Y)) ≫
        R₂.map (α₀.app (R₁.obj Y)) ≫ R₂.map (K₀.map (a.counit.app Y)) := by
    simp [mateEquiv]
  rw [e1, e1, ← b.unit_naturality_assoc, ← R₂.map_comp_assoc, h, R₂.map_comp_assoc,
    Category.assoc, ← R₂.map_comp, ← R₂.map_comp, ← t.naturality]
  simp only [Functor.map_comp, Category.assoc, Functor.id_obj]

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private theorem derivedComposition_fac'
    {A : Type uA} {B : Type uB} {C : Type*}
    [Category.{vA} A] [Category.{vB} B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at h
  exact h

private theorem interchange_fac (n : ℕᵒᵖ) (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map
          (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K) =
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app K) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex (.up ℤ)).obj K) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso FT EA).inv.app (DerivedCategory.Q.obj K))).mp
  dsimp only [FT, EA, EB]
  simp only [towerDerivedEvaluationInterchange, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact (derivedComposition_fac' EB F K).trans (derivedComposition_fac' FT EA K).symm

private theorem transition_fac {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors := rfl
  simp [towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

/-- The evaluation interchange of an exact functor commutes with the transitions.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: both natural transformations are determined on localized complexes, where the
interchange and the transitions are the strict evaluation identities. -/
theorem interchange_transition {m n : ℕᵒᵖ} (t : m ⟶ n) (M : DerivedCategory (ℕᵒᵖ ⥤ B)) :
    (towerDerivedEvaluationTransition A t).app
        (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.obj M) ≫
        (towerDerivedEvaluationInterchange F n).hom.app M =
      (towerDerivedEvaluationInterchange F m).hom.app M ≫
        F.mapDerivedCategory.map ((towerDerivedEvaluationTransition B t).app M) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let sA := towerDerivedEvaluationTransition A t
  let sB := towerDerivedEvaluationTransition B t
  have key : Functor.whiskerLeft FT.mapDerivedCategory sA ≫
      (towerDerivedEvaluationInterchange F n).hom =
      (towerDerivedEvaluationInterchange F m).hom ≫
        Functor.whiskerRight sB F.mapDerivedCategory := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))
    intro K
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    apply (cancel_mono (F.mapDerivedCategory.map
      (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app K) ≫
      F.mapDerivedCategoryFactors.hom.app
        ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K))).mp
    rw [Category.assoc, interchange_fac F n K, Category.assoc,
      ← F.mapDerivedCategory.map_comp_assoc, transition_fac t K]
    have h1 := sA.naturality (FT.mapDerivedCategoryFactors.hom.app K)
    have h2 := F.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ B).map t) (.up ℤ)).app K)
    have h3 := transition_fac t ((FT.mapHomologicalComplex (.up ℤ)).obj K)
    have h4 := interchange_fac F m K
    simp only [Functor.comp_map, Functor.comp_obj] at h1 h2
    rw [F.mapDerivedCategory.map_comp, Category.assoc, h2, ← reassoc_of% h1, h3]
    rw [reassoc_of% h4]
    rfl
  exact NatTrans.congr_app key M

end General

section Iso

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  {F : B ⥤ A} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : A ⥤ B} [G.Additive] [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] [Abelian A] [HasDerivedCategory A]
  [Abelian.HasKInjectiveResolutions A] in
private theorem isIso_of_kinjective_components'
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A]
    {E : Type*} [Category E] {V W : DerivedCategory A ⥤ E} (α : V ⟶ W)
    (h : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      IsIso (α.app (DerivedCategory.Q.obj I))) : IsIso α := by
  have : ∀ X, IsIso (α.app X) := by
    intro X
    obtain ⟨I, hI, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage X)
    have := hi
    have := h I hI
    let e : X ≅ DerivedCategory.Q.obj I :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map i)
    have ht : IsIso (V.map e.hom ≫ α.app (DerivedCategory.Q.obj I)) := inferInstance
    rw [α.naturality] at ht
    exact (isIso_comp_right_iff _ _).mp ht
  exact NatIso.isIso_of_isIso_app α

omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem cochainUnit_isIso' (G : A ⥤ B) [G.Additive] (I : CochainComplex A ℤ)
    [I.IsKInjective] : IsIso (cochainUnit G I) := by
  unfold cochainUnit
  infer_instance

private theorem derivedNatIso_refl'
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro I
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app I)).1
  erw [Functor.mapDerivedCategoryNatIso_fac]
  change F.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map (𝟙 _) =
    𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app I
  simp

omit [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [G.Additive] in
private theorem evaluation_localizedSquare' (n : ℕᵒᵖ) :
    localizedSquare ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) F
      ((evaluation ℕᵒᵖ B).obj n) ((evaluation ℕᵒᵖ A).obj n) (Iso.refl _) =
      (towerDerivedEvaluationInterchange F n).symm := by
  unfold localizedSquare towerDerivedEvaluationInterchange
  rw [derivedNatIso_refl']
  ext X
  simp

/-- The evaluation comparison of an exact adjunction is an isomorphism.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: on a K-injective tower complex, its normalization identifies it with the
derived unit of the evaluated K-injective complex, an isomorphism. -/
theorem evaluationComparison_isIso (a : F ⊣ G) (n : ℕᵒᵖ) :
    IsIso (evaluationComparison a n) := by
  apply isIso_of_kinjective_components'
  intro I hI
  have := hI
  have : CochainComplex.IsKInjective
      ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I) :=
    tower_evaluation_isKInjective A I n
  have := cochainUnit_isIso' ((Functor.whiskeringRight ℕᵒᵖ A B).obj G) I
  have hs := cochainUnit_isIso' G
    ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I)
  have ht := localized_mate_cochain_normalization (a.whiskerRight ℕᵒᵖ) a
    (g := (evaluation ℕᵒᵖ B).obj n) (h := (evaluation ℕᵒᵖ A).obj n) (Iso.refl _) I
  rw [evaluation_localizedSquare'] at ht
  have hm : (mateEquiv (a.whiskerRight ℕᵒᵖ) a
      (TwoSquare.mk ((evaluation ℕᵒᵖ B).obj n)
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) F ((evaluation ℕᵒᵖ A).obj n)
        (Iso.refl (((evaluation ℕᵒᵖ B).obj n) ⋙ F)).hom)) =
      𝟙 (((evaluation ℕᵒᵖ A).obj n) ⋙ G) := by
    ext T
    simp [mateEquiv]
  erw [hm] at ht
  have hid : (NatTrans.mapHomologicalComplex
      (𝟙 (((evaluation ℕᵒᵖ A).obj n) ⋙ G)) (.up ℤ)).app I = 𝟙 _ := by
    ext k
    rfl
  erw [hid, Functor.map_id, Category.id_comp] at ht
  rw [← ht] at hs
  simp only [isIso_comp_left_iff, isIso_comp_right_iff, Iso.symm_hom] at hs
  exact hs

end Iso

end CategoryTheory.UnboundedExactTower

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical mate of the pullback/evaluation comparison is invertible.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral). -/
instance pushEvaluationMap_isIso {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ) :
    IsIso (pushEvaluationMap l E f n) :=
  UnboundedExactTower.evaluationComparison_isIso
    (CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f) (op n)

/-- Pullback of towers is exact, commutes with evaluation, and the derived pushforward
commutes with derived evaluation compatibly with units, counits and transitions.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: pullback is levelwise exact. The comparisons are the mates of the exact evaluation
interchanges, invertible by K-injective normalization; the unit and counit equations are
the mate identities, and the transition equation follows from compatibility of the
interchanges with the transitions. -/
theorem pullback_properties {T T' : Scheme.{u}} (f : T' ⟶ T) :
    PreservesFiniteLimits (pull l E f) ∧
      PreservesFiniteColimits (pull l E f) ∧
      (∀ n : ℕ, pull l E f ⋙ ev l E T' n =
        ev l E T n ⋙ CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) ∧
      ∃ β : ∀ n : ℕ, rpush l E f ⋙ dev l E T n ≅ dev l E T' n ⋙ rpushModule l E f,
        (∀ n : ℕ, (β n).hom = pushEvaluationMap l E f n) ∧
        (∀ (n : ℕ) (M : DTow l E T),
          (dev l E T n).map ((towerAdjunction l E f).unit.app M) ≫
              (β n).hom.app ((dpull l E f).obj M) =
            (moduleAdjunction l E f).unit.app ((dev l E T n).obj M) ≫
              (rpushModule l E f).map ((pullEvaluation l E f n).inv.app M)) ∧
        (∀ (n : ℕ) (N : DTow l E T'),
          (dev l E T' n).map ((towerAdjunction l E f).counit.app N) =
            (pullEvaluation l E f n).hom.app ((rpush l E f).obj N) ≫
              (dpullModule l E f).map ((β n).hom.app N) ≫
              (moduleAdjunction l E f).counit.app ((dev l E T' n).obj N)) ∧
        (∀ (n : ℕ) (M : DTow l E T'),
          (transition l E T n).app ((rpush l E f).obj M) ≫ (β n).hom.app M =
            (β (n+1)).hom.app M ≫ (rpushModule l E f).map
              ((transition l E T' n).app M)) := by
  refine ⟨inferInstance, inferInstance, fun n ↦ rfl,
    fun n ↦ asIso (pushEvaluationMap l E f n), fun n ↦ rfl, ?_, ?_, ?_⟩
  · intro n M
    exact unit_mateEquiv _ _ _ M
  · intro n N
    have h := mateEquiv_counit (towerAdjunction l E f) (moduleAdjunction l E f)
      (.mk _ _ _ _ (pullEvaluation l E f n).inv) N
    dsimp only [asIso_hom, pushEvaluationMap]
    erw [h]
    simp
  · intro n M
    apply UnboundedExactTower.mateEquiv_whisker_app
    intro X
    have h := UnboundedExactTower.interchange_transition
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)
      (homOfLE (Nat.le_succ n)).op X
    dsimp only [pullEvaluation, transition]
    rw [← cancel_epi ((towerDerivedEvaluationInterchange _ (op (n + 1))).hom.app X),
      ← reassoc_of% h]
    simp

end CompleteDerivedCompletion

end AlgebraicGeometry.ProEtale
