/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackCanonicalComparison
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedRealizedUnitTransport
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Canonical derived diagonal realization endpoint comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_single_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ P ≅ H ⋙ V) (M : A) :
    (Functor.mapDerivedCategorySquareIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      V.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (H.obj M) =
    P.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (s.hom.app M) := by
  dsimp only [Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U P).inv.app
    ((DerivedCategory.singleFunctor A 0).obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor U P M)]

private theorem derived_endpoint_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (M : A) {N : B} {P : C} {Q : D}
    (d : F.obj M ≅ N) (s : H.obj M ≅ P) (x : G.obj N ≅ Q) (u : I.obj P ≅ Q)
    (L : DerivedCategory C ⥤ DerivedCategory D) (q : L ≅ I.mapDerivedCategory)
    (ho : e.hom.app M ≫ I.map s.hom ≫ u.hom = G.map d.hom ≫ x.hom) :
    (Functor.mapDerivedCategorySquareIso e ≪≫
        Functor.isoWhiskerLeft H.mapDerivedCategory q.symm).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
      L.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map s.hom) ≫
      ((q.hom.app ((DerivedCategory.singleFunctor C 0).obj P) ≫
        (I.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
        (DerivedCategory.singleFunctor D 0).map u.hom) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map d.hom) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D 0).map x.hom) := by
  have hs := derived_single_square F G H I e M
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] at hs
  simp only [Category.assoc] at hs
  have hnS := (I.mapDerivedCategorySingleFunctor 0).hom.naturality s.hom
  have hnX := (G.mapDerivedCategorySingleFunctor 0).hom.naturality d.hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnS hnX
  have hgeom {V W : DerivedCategory C} (g : V ⟶ W) :
      q.inv.app V ≫ L.map g ≫ q.hom.app W = I.mapDerivedCategory.map g := by
    rw [← q.inv.naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.mapDerivedCategorySquareIso]
  simp only [Category.assoc]
  rw [reassoc_of% hgeom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnS, reassoc_of% hs]
  have hh := congrArg (DerivedCategory.singleFunctor D 0).map ho
  simp only [Functor.map_comp] at hh
  rw [hh, ← reassoc_of% hnX]

private theorem ordinary_mate_endpoint
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {L : C ⥤ D} {Q : D ⥤ C}
    (adj : F ⊣ R) (adjb : L ⊣ Q) (U : A ⥤ C) (V : B ⥤ D)
    (c : F ⋙ V ≅ U ⋙ L) (t : R ⋙ U ≅ V ⋙ Q)
    (ht : ∀ (M : A) (N : B) (m : F.obj M ⟶ N),
      adjb.homEquiv _ _ (c.inv.app M ≫ V.map m) =
        U.map (adj.homEquiv M N m) ≫ t.hom.app N)
    (MS : A) (MX : B) (US : C) (UX : D)
    (d : F.obj MS ≅ MX) (s : U.obj MS ≅ US) (x : V.obj MX ≅ UX)
    (u : L.obj US ≅ UX)
    (he : U.map (adj.homEquiv MS MX d.hom) ≫ t.hom.app MX ≫ Q.map x.hom =
      s.hom ≫ adjb.homEquiv _ _ u.hom) :
    c.hom.app MS ≫ L.map s.hom ≫ u.hom = V.map d.hom ≫ x.hom := by
  apply (cancel_epi (c.inv.app MS)).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (c.inv.app MS)]
  apply (adjb.homEquiv _ _).injective
  rw [adjb.homEquiv_naturality_left, adjb.homEquiv_naturality_right, ht]
  simpa only [Category.assoc] using he.symm

private theorem ordinary_bridge_endpoint
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {L : C ⥤ D} {Q : D ⥤ C}
    (adj : F ⊣ R) (adjb : L ⊣ Q) (U : A ⥤ C) (V : B ⥤ D)
    (R' : B ⥤ A) (b : R' ≅ R) (o : R' ⋙ U ≅ V ⋙ Q)
    (c : F ⋙ V ≅ U ⋙ L) (t : R ⋙ U ≅ V ⋙ Q)
    (ht : ∀ (M : A) (N : B) (m : F.obj M ⟶ N),
      adjb.homEquiv _ _ (c.inv.app M ≫ V.map m) =
        U.map (adj.homEquiv M N m) ≫ t.hom.app N)
    (htiso : t = Functor.isoWhiskerRight b.symm U ≪≫ o)
    (MS : A) (MX : B) (US : C) (UX : D)
    (d : F.obj MS ≅ MX) (s : U.obj MS ≅ US) (x : V.obj MX ≅ UX)
    (u : L.obj US ≅ UX) (m : MS ⟶ R'.obj MX) (v : L.obj US ⟶ UX)
    (hm : adj.homEquiv MS MX d.hom = m ≫ b.hom.app MX)
    (hu : adjb.homEquiv US UX u.hom = adjb.homEquiv US UX v)
    (ho : U.map m ≫ o.hom.app MX ≫ Q.map x.hom =
      s.hom ≫ adjb.homEquiv US UX v) :
    c.hom.app MS ≫ L.map s.hom ≫ u.hom = V.map d.hom ≫ x.hom := by
  apply ordinary_mate_endpoint adj adjb U V c t ht MS MX US UX d s x u
  rw [htiso, hm, hu]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.whiskerRight_app]
  simp only [Functor.map_comp, Category.assoc]
  have hb := congrArg U.map (b.hom_inv_id_app MX)
  rw [Functor.map_comp, U.map_id] at hb
  rw [reassoc_of% hb]
  exact ho

private theorem completed_unit_adjunct
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
        d.completedUnit.hom =
      DiagonalTrace.completedPushUnit l f ≫ (diagonalPullbackPushBridge l f).hom.app _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact d.completedUnit_normalization U a

private theorem condensed_unit_adjunct
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S)
    (unit : UnitPullEndpoint R f) :
    (CondensedRing.upperStarLowerStarAdjunction R f).homEquiv _ _ unit.iso.hom =
      (CondensedRing.upperStarLowerStarAdjunction R f).homEquiv _ _
        (Functor.Monoidal.εIso (CondensedRing.upperStar R f)).inv := by
  apply Mod.hom_ext
  exact unit.normalization.trans (CondensedRing.homEquiv_εIso_inv_hom R f).symm

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  purZlReduction sfbConstantRingAbIso

private theorem source_unit_equation
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (square : CompletedOrdinarySquare l f eX eS) :
    eS.F.map (DiagonalTrace.completedPushUnit l f) ≫ square.ordinary.hom.app _ ≫
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
          eX.unitIso.hom =
      eS.unitIso.hom ≫
        (CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _
          (Functor.Monoidal.εIso (CondensedRing.upperStar
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)).inv :=
  completed_ordinary_unit_general l f eS eX square.ordinary square.normalization

private theorem right_comparison_eq
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) :
    diagonalPullbackRightComparison l f eX eS =
      Functor.isoWhiskerRight (diagonalPullbackPushBridge l f).symm eS.F ≪≫
        (Classical.choice (completedCoefficientOrdinarySquare_exists l f eX eS)).ordinary :=
  rfl

-- Literal endpoints keep the kernel from unfolding the inverse mate to compare aliases.
private theorem ordinary_unit_component
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalPullbackOrdinaryComparison l f eX eS).hom.app
        (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))) ≫
      (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        eS.unitIso.hom ≫ unit.iso.hom =
    eX.F.map d.completedUnit.hom ≫ eX.unitIso.hom := by
  exact ordinary_bridge_endpoint
    (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    eS.F eX.F (diagonalTracePush l f) (diagonalPullbackPushBridge l f)
    (Classical.choice (completedCoefficientOrdinarySquare_exists l f eX eS)).ordinary
    (diagonalPullbackOrdinaryComparison l f eX eS)
    (diagonalPullbackRightComparison l f eX eS)
    (diagonalPullbackOrdinaryComparison_transpose l f eX eS)
    (right_comparison_eq l f eX eS)
    (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
    (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))
    _ _ d.completedUnit eS.unitIso eX.unitIso unit.iso
    (DiagonalTrace.completedPushUnit l f)
    (Functor.Monoidal.εIso (CondensedRing.upperStar
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)).inv
    (completed_unit_adjunct l f d)
    (condensed_unit_adjunct (Profinite.continuousMapRingObj.{u} ℤ_[l]) f unit)
    (source_unit_equation l f eX eS
      (Classical.choice (completedCoefficientOrdinarySquare_exists l f eX eS)))

private theorem single_pullback_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules Λ S) :
    singlePullback Λ f M =
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).app
          ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj M) ≪≫
        ((CondensedRing.upperStar Λ f).mapDerivedCategorySingleFunctor 0).app M := rfl

private theorem derived_comparison_eq
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) :
    diagonalPullbackDerivedComparison l f eX eS =
      Functor.mapDerivedCategorySquareIso (diagonalPullbackOrdinaryComparison l f eX eS) ≪≫
        Functor.isoWhiskerLeft eS.F.mapDerivedCategory
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).symm := rfl

private theorem canonical_derived_unit
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalPullbackDerivedComparison l f eX eS).hom.app
        (DiagonalTrace.completedUnit l S) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.singleUnit l S) ≫ unit.derived =
    eX.F.mapDerivedCategory.map
      ((Scheme.proEtaleRingModulePullback f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (diagonalPullbackCoefficientIso l f)).mapDerivedCategorySingleFunctor 0 |>.app
          (SheafOfModules.unit (Scheme.purTwistRing S
            (Scheme.purTwistZlCompletion S l)))
        |>.trans ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
          d.completedUnit)).hom ≫ eX.singleUnit l X := by
  rw [derived_comparison_eq]
  simp only [CompletedRealization.singleUnit, PullEndpoint.derived, single_pullback_eq,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  exact derived_endpoint_square
    (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    eX.F eS.F (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (diagonalPullbackOrdinaryComparison l f eX eS)
    (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
    d.completedUnit eS.unitIso eX.unitIso unit.iso
    (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (ordinary_unit_component l f eX eS unit d)

set_option linter.unusedVariables false in
-- The fixed public signature retains invertibility and line endpoint parameters.
/-- The canonical derived comparison has the prescribed completed-unit component.
Source: diagonal coefficient changes paragraph (3), endpoint transport.
(blueprint: lem-sfb-diagonal-realization-pullback-unit-component).

Proof: use `hc` to identify the coefficient isomorphism with the canonical one.
At the ordinary completed unit, cancel the ordinary comparison isomorphism and apply
the condensed upper-star adjunction's Hom bijection. Its transpose is the formula
`diagonalPullbackOrdinaryComparison_transpose`. The normalization of the ordinary
right square identifies its underlying sheaf map with direct image of the realization
comparison. The completed-unit adjoint normalization in `d`, the scalar direct-image
formula for completed realization, and the specified normalization of `unit` identify
the two transposes. Faithfulness after forgetting module action gives the ordinary
unit equation. Apply the exact-derived square and its single-functor component
formulas. Insert `eS.singleUnit` and `eX.singleUnit`, cancel the canonical geometric
upper-star comparison, and use naturality of the single comparison. This gives
precisely the displayed derived equation. -/
theorem diagonalRealization_pullback_unit_component
    (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f)
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f coeff) :
    (diagonalRealization_pullback_canonical_comparison l f eX eS coeff hc).hom.app
      (DiagonalTrace.completedUnit l S) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.singleUnit l S) ≫ unit.derived =
    eX.F.mapDerivedCategory.map
      ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategorySingleFunctor 0 |>.app
          (SheafOfModules.unit (Scheme.purTwistRing S
            (Scheme.purTwistZlCompletion S l)))
        |>.trans ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
          d.completedUnit)).hom ≫ eX.singleUnit l X := by
  have hmap : IsIso (diagonalCompletedCoefficientMap l f) := by
    rw [← hc]
    infer_instance
  letI := hmap
  have hcoeff : coeff = diagonalPullbackCoefficientIso l f := Iso.ext hc
  subst coeff
  rw [diagonalRealization_pullback_canonical_comparison_normalized]
  exact canonical_derived_unit l f eX eS unit d

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
