/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import all WeilConjectures.SmoothBaseChange.AdicFiniteExchangeEncoding
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedConstructiblePreservation
import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import WeilConjectures.AlgebraicGeometry.Sf.SfConstructibleCanonicalCompleteness
import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalReduction

/-!
# Completed coefficient transport and Weil categories

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `pbcIsoModulePullback`, `pbcIsoAmbientPullback`: exact coefficient transport.
- `pbcIsoCompletedPullback_identification`: the completed-pullback identification.
- `pbcRationalIsoPullback`: transport on the raw rational coefficient category.
- `pbcIsoRationalScalarComparison`: the normalized scalar/transport comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportCochainDerivedCounit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))] :
    ∃ εc : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      L.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ P, εc.app P = Functor.leftDerivedCounitOnComplex G L ε P := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let εc : DerivedCategory.Q ⋙ L ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app := fun P ↦ ε.app (π.obj P)
      naturality := fun _ _ f ↦ ε.naturality (π.map f) }
  refine ⟨εc, ?_, ?_⟩
  swap
  · intro P
    simp only [εc, Functor.leftDerivedCounitOnComplex,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      Functor.mapHomotopyCategoryFactors]
    erw [L.map_id, DerivedCategory.Qh.map_id]
    change ε.app (π.obj P) = 𝟙 _ ≫ ε.app (π.obj P) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · refine ⟨⟨⟨?_⟩⟩⟩
    let lift (Z : DerivedCategory A ⥤ DerivedCategory B)
        (τ : DerivedCategory.Q ⋙ Z ⟶
          G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
        DerivedCategory.Qh ⋙ Z ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
      { app := fun X ↦ τ.app X.as
        naturality := by
          intro X Y f
          obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
          obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
          obtain ⟨f, rfl⟩ := π.map_surjective f
          exact τ.naturality f }
    refine IsTerminal.ofUniqueHom (fun Z ↦ CostructuredArrow.homMk
      (L.leftDerivedLift ε (HomotopyCategory.quasiIso A (.up ℤ)) Z.left
        (lift Z.left Z.hom)) (by
          apply NatTrans.ext
          funext P
          exact L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
            Z.left (lift Z.left Z.hom) (π.obj P))) ?_
    intro Z m
    apply CostructuredArrow.hom_ext
    apply L.leftDerived_ext ε (HomotopyCategory.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext X
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have hm := NatTrans.congr_app m.w P
    have hm' : m.left.app (DerivedCategory.Q.obj P) ≫ ε.app (π.obj P) =
        Z.hom.app P := by simpa using hm
    exact hm'.trans
      (L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
        Z.left (lift Z.left Z.hom) (π.obj P)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportDerivedSquare
    {A B AD BD : Type*} [Category A] [Category B] [Category AD] [Category BD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (G : A ⥤ B) (L : AD ⥤ BD)
    (ε : QA ⋙ L ⟶ G ⋙ QB) [L.IsRightKanExtension ε]
    (U : A ⥤ A) [U.IsEquivalence] (V : B ⥤ B)
    (HA : AD ⥤ AD) [HA.IsEquivalence] (HB : BD ⥤ BD) [HB.IsEquivalence]
    (θA : QA ⋙ HA ≅ U ⋙ QA) (θB : QB ⋙ HB ≅ V ⋙ QB)
    (τ : G ⋙ V ≅ U ⋙ G) :
    ∃! c : L ⋙ HB ≅ HA ⋙ L, ∀ P : A,
      c.hom.app (QA.obj P) ≫ L.map (θA.hom.app P) ≫ ε.app (U.obj P) =
        HB.map (ε.app P) ≫ θB.hom.app (G.obj P) ≫ QB.map (τ.hom.app P) := by
  let εU := (Functor.associator U QA L).hom ≫ Functor.whiskerLeft U ε
  have : L.IsRightKanExtension εU :=
    (Functor.isRightKanExtension_iff_precomp L U ε).mp inferInstance
  let δ := (Functor.associator QA HA L).inv ≫
    Functor.whiskerRight θA.hom L ≫ εU
  have : (HA ⋙ L).IsRightKanExtension δ :=
    (Functor.isRightKanExtension_iff_postcomp₁ HA θA εU).mp inferInstance
  let σ := (Functor.associator QA L HB).inv ≫ Functor.whiskerRight ε HB
  have : (L ⋙ HB).IsRightKanExtension σ :=
    Functor.isRightKanExtension_comp_of_isEquivalence L ε HB
  let ζ : (G ⋙ QB) ⋙ HB ≅ U ⋙ G ⋙ QB :=
    Functor.associator G QB HB ≪≫ Functor.isoWhiskerLeft G θB ≪≫
      (Functor.associator G V QB).symm ≪≫ Functor.isoWhiskerRight τ QB ≪≫
      Functor.associator U G QB
  let c := Functor.rightKanExtensionUniqueOfIso (L ⋙ HB) σ ζ (HA ⋙ L) δ
  have hc (P : A) :
      c.hom.app (QA.obj P) ≫ L.map (θA.hom.app P) ≫ ε.app (U.obj P) =
        HB.map (ε.app P) ≫ θB.hom.app (G.obj P) ≫ QB.map (τ.hom.app P) := by
    have h := (HA ⋙ L).liftOfIsRightKanExtension_fac_app δ (L ⋙ HB) (σ ≫ ζ.hom) P
    change c.hom.app (QA.obj P) ≫ δ.app P = (σ ≫ ζ.hom).app P at h
    simpa only [δ, εU, σ, ζ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.map_id, Category.id_comp,
      Category.comp_id, Category.assoc] using h
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply (HA ⋙ L).hom_ext_of_isRightKanExtension δ
  apply NatTrans.ext
  funext P
  simpa only [δ, εU, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc] using (hc' P).trans (hc P).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isoTransportCochainSquare
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : A ⥤ B) [hG : G.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)))
    (FE : A ⥤ A) (FF : B ⥤ B) [hFA : FE.Additive] [hFB : FF.Additive]
    [hEA : FE.IsEquivalence] [hEB : FF.IsEquivalence]
    (τ : G.mapHomologicalComplex (.up ℤ) ⋙ FF.mapHomologicalComplex (.up ℤ) ≅
      FE.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) :
    ∃! c : L ⋙ FF.mapDerivedCategory ≅ FE.mapDerivedCategory ⋙ L,
      ∀ P : CochainComplex A ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          L.map (FE.mapDerivedCategoryFactors.hom.app P) ≫
          Functor.leftDerivedCounitOnComplex G L ε
            ((FE.mapHomologicalComplex (.up ℤ)).obj P) =
        FF.mapDerivedCategory.map (Functor.leftDerivedCounitOnComplex G L ε P) ≫
          FF.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (τ.hom.app P) := by
  let : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := hL
  obtain ⟨εc, hεc, hεapp⟩ := isoTransportCochainDerivedCounit G L ε
  let : L.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ)) := hεc
  let : L.IsRightKanExtension εc := Functor.IsLeftDerivedFunctor.isRightKanExtension
    L εc (HomologicalComplex.quasiIso A (.up ℤ))
  let : (FE.mapHomologicalComplex (.up ℤ)).IsEquivalence :=
    (FE.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  obtain ⟨c, hc, hu⟩ := isoTransportDerivedSquare DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) L εc
    (FE.mapHomologicalComplex (.up ℤ)) (FF.mapHomologicalComplex (.up ℤ))
    FE.mapDerivedCategory FF.mapDerivedCategory FE.mapDerivedCategoryFactors
    FF.mapDerivedCategoryFactors τ
  refine ⟨c, ?_, ?_⟩
  · intro P
    simpa only [hεapp] using hc P
  · intro c' hc'
    apply hu c'
    intro P
    simpa only [hεapp] using hc' P

namespace AlgebraicGeometry.Scheme

private theorem isoTransportComplexCounitEq {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules X R) ℤ) :
    pbcComplexCounit φ P = Functor.leftDerivedCounitOnComplex (pbcExtend φ)
      (pbcDerivedExtend φ) (pbcExtensionCounit φ) P := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

include hf in
set_option linter.unusedSectionVars false in
/-- The coefficient map is invertible for a scheme isomorphism. -/
@[instance] theorem pbcIsoCoefficientMap_isIso : IsIso (completedCoefficientMap f d) := by
  rw [completedCoefficientMap_eq_integralRingIso]
  infer_instance

/-- Exact module transport: inverse image followed by the canonical scalar identification. -/
abbrev pbcIsoModulePullback :
    pbcModules Y (pbcAdicCompletion Y d) ⥤ pbcModules X (pbcAdicCompletion X d) :=
  proEtaleRingModulePullback f (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
    (asIso (completedCoefficientMap f d))

private theorem isoSiteModulePushforward
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (E : C ≌ D) [E.functor.IsContinuous J K] [E.inverse.IsContinuous K J]
    {R : Sheaf K RingCat.{u + 1}} {S : Sheaf J RingCat.{u + 1}}
    (φ : S ⟶ (E.functor.sheafPushforwardContinuous RingCat J K).obj R) [IsIso φ] :
    (SheafOfModules.pushforward.{u + 1} φ).IsEquivalence := by
  let F := E.functor
  let G := E.inverse
  let a := E.toAdjunction.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat K J).obj S :=
    a.unit.app R ≫ (G.sheafPushforwardContinuous RingCat K J).map (inv φ)
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, a]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) S.obj = 𝟙 S.obj := by
    have hh : φ ≫ (F.sheafPushforwardContinuous RingCat J K).map ψ ≫
        a.counit.app S = 𝟙 S := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [a.counit.naturality (inv φ)]
      have ht := a.left_triangle_components R
      calc
        _ = φ ≫ ((F.sheafPushforwardContinuous RingCat J K).map
            (a.unit.app R) ≫ a.counit.app
              ((F.sheafPushforwardContinuous RingCat J K).obj R)) ≫ inv φ := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ inv φ := congrArg (fun z ↦ φ ≫ z ≫ inv φ) ht
        _ = _ := by simp
    exact congrArg (fun z ↦ z.hom) hh
  exact (SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂).isEquivalence_functor

/-- The module pullback is an exact equivalence with inverse transport along f inverse. -/
@[instance] theorem pbcIsoModulePullback_isEquivalence :
    (pbcIsoModulePullback f d).IsEquivalence := by
  let hsite : (proEtaleIsoPostcompose f).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence f).1
  let : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale f)).IsEquivalence := hsite
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial
  let hbase : (proEtaleBaseChange f).IsEquivalence :=
    a.isEquivalence_right_of_isEquivalence_left
  let E : Y.ProEt ≌ X.ProEt := a.toEquivalence.symm
  let : E.functor.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    inferInstanceAs ((proEtaleBaseChange f).IsContinuous _ _)
  let hcont : E.inverse.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous f
  let hu : IsIso (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, u, u} f CommRingCat.{u + 1}).2.1
  let hm : IsIso (proEtaleRingDirectImageMap f
      (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (asIso (completedCoefficientMap f d))) := by
    dsimp only [proEtaleRingDirectImageMap]
    infer_instance
  let hright : (proEtaleRingModuleDirectImage f
      (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (asIso (completedCoefficientMap f d))).IsEquivalence := by
    let φ : (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (pbcAdicCompletion Y d) ⟶
        ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat
          (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (pbcAdicCompletion X d)) :=
      ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d)
        (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    let : IsIso φ := by
      change IsIso ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (proEtaleRingDirectImageMap f (pbcAdicCompletion Y d)
            (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))))
      infer_instance
    exact isoSiteModulePushforward E φ
  exact (proEtaleRingModuleAdjunction f _ _
    (asIso (completedCoefficientMap f d))).isEquivalence_left_of_isEquivalence_right

attribute [local irreducible] proEtaleRingModulePullback completedModulePullback
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  completedPullbackComparison completedPullbackObject
  completedCoefficientMap

/-- The exact equivalence transported to complexes and localized at quasi-isomorphisms. -/
abbrev pbcIsoAmbientPullback : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d :=
  (pbcIsoModulePullback f d).mapDerivedCategory

/-- The two recorded ordinary inverse images have the same tensor object and map formulas.
-/
theorem pbcIsoModulePullback_eq_completed :
    pbcIsoModulePullback f d = completedModulePullback f d := by
  rw [completedModulePullback_eq_exact]
  have h : asIso (completedCoefficientMap f d) = d.integralRingIso f := by
    apply Iso.ext
    exact completedCoefficientMap_eq_integralRingIso f d
  exact congrArg (proEtaleRingModulePullback f (d.completedRing Y) (d.completedRing X)) h

private theorem isoExactDerivedComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (he : G = F)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! alpha : L ≅ G.mapDerivedCategory,
      ∀ P : CochainComplex C ℤ,
        alpha.hom.app (DerivedCategory.Q.obj P) ≫
            G.mapDerivedCategoryFactors.hom.app P =
          F.leftDerivedCounitOnComplex L ε P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (eqToIso he).symm (.up ℤ)).hom.app P) := by
  cases he
  have hid (P : CochainComplex C ℤ) :
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (eqToIso (rfl : F = F)).symm (.up ℤ)).hom.app P) =
          𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Q.map_id _
  simp_rw [hid, Category.comp_id]
  exact exactDerivedCounitComparison F L ε

/-- Exact descent is the unique ordinary derived inverse image with its universal counit.
-/
theorem pbcIsoOrdinaryDerivedComparison_exists :
    ∃! alpha : completedOrdinaryPullback f d ≅ pbcIsoAmbientPullback f d,
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        alpha.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcIsoModulePullback f d).mapDerivedCategoryFactors.hom.app P =
          completedOrdinaryPullbackComplexCounit f d P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (eqToIso (pbcIsoModulePullback_eq_completed f d)).symm (.up ℤ)).hom.app P) := by
  exact isoExactDerivedComparison (completedModulePullback f d) (pbcIsoModulePullback f d)
    (pbcIsoModulePullback_eq_completed f d) (completedOrdinaryPullback f d)
    (completedOrdinaryPullbackCounit f d)

/-- The comparison fixed by the two derived counits on every complex. -/
def pbcIsoOrdinaryDerivedComparison :=
  (pbcIsoOrdinaryDerivedComparison_exists f d).exists.choose

private theorem isoTransportIntrinsicIso
    (S : Scheme.{u}) {M N : PbcCompletedDerived S d} (i : M ≅ N)
    (hM : PbcIsIntrinsicallyComplete S d M) : PbcIsIntrinsicallyComplete S d N := by
  obtain ⟨r, a, ha, C, eC, hC⟩ := hM
  refine ⟨r, a, ha, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison S d).inv).mapIso i, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

omit hf in
private theorem isoTransportDirectComplete
    (M : PbcCompletedDerived X d) (hM : PbcIsIntrinsicallyComplete X d M) :
    PbcIsIntrinsicallyComplete Y d ((pbcActualDerivedPush f d).obj M) := by
  let P : ObjectProperty (PbcCompletedDerived X d) := PbcIsIntrinsicallyComplete X d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  have hu : IsIso ((pbcActualCompletionUnit d X).app M) :=
    adj.isIso_unit_app_of_iso (X := ⟨M, hM⟩) (Iso.refl M)
  obtain ⟨c, hc⟩ := (pbcActualDirectCompletionIso_exists f d).exists
  have hv : IsIso ((pbcActualCompletionUnit d Y).app
      ((pbcActualDerivedPush f d).obj M) ≫ c.hom.app M) := by
    rw [hc]
    infer_instance
  have : IsIso ((pbcActualCompletionUnit d Y).app
      ((pbcActualDerivedPush f d).obj M)) :=
    IsIso.of_isIso_comp_right _ (c.hom.app M)
  exact isoTransportIntrinsicIso d Y
    (asIso ((pbcActualCompletionUnit d Y).app
      ((pbcActualDerivedPush f d).obj M))).symm
    (((ObjectProperty.ι (PbcIsIntrinsicallyComplete Y d)).leftAdjoint.obj
      ((pbcActualDerivedPush f d).obj M)).property)

/-- Intrinsic completion preservation component of the automorphism transport. -/
theorem pbcIsoAmbientPullback_preserves_intrinsic
    (K : PbcBoundedConstructibleComplete Y d)
    (H : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d)
    (e : completedOrdinaryPullback f d ≅ H) :
    PbcIsIntrinsicallyComplete X d (H.obj K.obj) := by
  let G := completedOrdinaryPullback (inv f) d
  have : G.IsEquivalence := Functor.isEquivalence_of_iso
    (pbcIsoOrdinaryDerivedComparison (inv f) d).symm
  let adj := pbcActualDerivedAdjunction (inv f) d
  let c : completedOrdinaryPullback f d ⋙ G ≅ 𝟭 (PbcCompletedDerived Y d) :=
    (pbcActualDerivedPullCompIso (inv f) f d).symm ≪≫
      eqToIso (congrArg (fun g ↦ completedOrdinaryPullback g d) (IsIso.inv_hom_id f)) ≪≫
      pbcActualDerivedPullIdIso d Y
  let t : completedOrdinaryPullback f d ≅ pbcActualDerivedPush (inv f) d :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (asIso adj.unit) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c _ ≪≫ Functor.leftUnitor _
  exact isoTransportIntrinsicIso d X ((t.symm ≪≫ e).app K.obj)
    (isoTransportDirectComplete (inv f) d K.obj K.property.1)

private theorem pbcTransition_naturality
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    {E F : DerivedCategory (pbcModules T R)} (q : E ⟶ F) :
    (pbcDerivedExtend a).map q ≫ pbcReductionTransition a b c h F =
      pbcReductionTransition a b c h E ≫
        (pbcDerivedRestrict b).map ((pbcDerivedExtend c).map q) := by
  unfold pbcReductionTransition
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  rw [← Category.assoc, ← (pbcDerivedScalarAdjunction c).unit_naturality q]
  simp only [Category.assoc]
  congr 1
  exact (pbcDerivedRestrictComp a b c h).inv.naturality ((pbcDerivedExtend c).map q)

private theorem uniformReductions_iso_transport
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {L M : PbcCompletedDerived T d}
    (e : L ≅ M) (hL : PbcHasUniformConstructibleReductions T d L) :
    PbcHasUniformConstructibleReductions T d M := by
  obtain ⟨W, w, hW, hw⟩ := hL
  refine ⟨W, fun n ↦ w n ≪≫ (pbcCompletedReduction T d n).mapIso e, hW, ?_⟩
  intro b a hab
  dsimp
  rw [Functor.map_comp]
  change _ ≫ (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (w a).hom ≫
      (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
        ((pbcCompletedReduction T d a).map e.hom) = _
  rw [← Category.assoc, hw b a hab]
  simp only [Category.assoc]
  rw [pbcTransition_naturality]

private def isoTransportStratification (S : Stratification Y) : Stratification X where
  n := S.n
  stratum i := f ⁻¹' S.stratum i
  isLocallyClosed_stratum i := (S.isLocallyClosed_stratum i).preimage f.continuous
  isConstructible_stratum i := f.isConstructible_preimage (S.isConstructible_stratum i)
  iUnion_stratum_eq_univ := by
    rw [← Set.preimage_iUnion, S.iUnion_stratum_eq_univ, Set.preimage_univ]
  pairwise_disjoint_stratum i j hij := (S.pairwise_disjoint_stratum hij).preimage _
  domain := S.domain
  immersion i := S.immersion i ≫ inv f
  range_immersion i := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, S.range_immersion]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change f ((inv f) y) ∈ S.stratum i
      rw [← Hom.comp_apply, IsIso.inv_hom_id]
      exact hy
    · intro hx
      refine ⟨f x, hx, ?_⟩
      change (f ≫ inv f) x = x
      rw [IsIso.hom_inv_id]
      rfl

/-- Uniform reduction preservation component of the automorphism transport. -/
theorem pbcIsoAmbientPullback_preserves_reductions
    (K : PbcBoundedConstructibleComplete Y d)
    (H : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d)
    (e : completedOrdinaryPullback f d ≅ H) :
    PbcHasUniformConstructibleReductions X d (H.obj K.obj) := by
  classical
  obtain ⟨M, eK, hM, heK⟩ := K.property.2.1
  obtain ⟨a, b, hab, S, hS⟩ := hM
  let N := pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K.obj)
  have hN : IsUniformlyBoundedConstructibleAdicTower d N := by
    refine ⟨a, b, hab, isoTransportStratification f S, ?_⟩
    intro i
    obtain ⟨V, hV, hL⟩ := hS i
    refine ⟨V, hV, ?_⟩
    intro U q hq
    obtain ⟨L⟩ := hL U q hq
    let g := U.hom ≫ S.immersion i
    obtain ⟨ha, hf⟩ := pbcIsoLocalComplex_properties f d g M a b L
    obtain ⟨j, hj⟩ := pbcIsoLocalComplex_reduction_comparison f d g K.obj M eK heK a b L
    have model : Nonempty (AdicTowerLocalModel d (g ≫ inv f) N a b) :=
      ⟨{
        complex := pbcIsoLocalComplex f d g L.complex
        bounded := fun q hq ↦
          (pbcRestrict (pbcIsoLocalCoefficient f d g).hom).map_isZero (L.bounded q hq)
        adicLisse := ha
        finiteLisse := hf
        identification := j
        compatible := hj }⟩
    simpa only [g, isoTransportStratification, Category.assoc] using model
  have hOrd : PbcHasUniformConstructibleReductions X d
      ((completedOrdinaryPullback f d).obj K.obj) := by
    refine ⟨N, fun _ ↦ Iso.refl _, hN, ?_⟩
    intro b a hab
    dsimp only [N, pbcReductionAdicTower, Iso.refl_hom]
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    dsimp only [adicTowerSemilinearTransition, pbcReductionNormalization,
      pbcReductionNormalizationHom]
    exact ((pbcDerivedScalarAdjunction (pbcAdicQuotient X d b a hab)).homEquiv _ _
      |>.apply_symm_apply _)
  exact uniformReductions_iso_transport d (e.app K.obj) hOrd

/-- Compatible etale-origin preservation component of the automorphism transport. -/
theorem pbcIsoAmbientPullback_preserves_origins
    (K : PbcBoundedConstructibleComplete Y d)
    (H : PbcCompletedDerived Y d ⥤ PbcCompletedDerived X d)
    (e : completedOrdinaryPullback f d ≅ H) :
    PbcHasCompatibleEtaleOrigins X d (H.obj K.obj) := by
  classical
  obtain ⟨P, eP, _⟩ := K.property.2.2
  let M (n : ℕ) :=
    (ProEtale.upperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f).mapDerivedCategory.obj
      (P.K n)
  have origins (n : ℕ) :
      ∃ hM : DerivedCategory.TStructure.t.plus
          ((ProEtale.finiteCoefficientRealization X
            (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj (M n)),
        Nonempty (EtaleOriginWitness X (ProEtale.PbcQuotient d n)
          ⟨(ProEtale.finiteCoefficientRealization X
            (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj (M n), hM⟩) := by
    let Q := ProEtale.PbcQuotient d n
    let U := ProEtale.upperStar (ModuleCat.{u + 1} Q) f
    let V := Etale.upperStar (ModuleCat.{u + 1} Q) f
    let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q) X
    let R := ProEtale.finiteCoefficientRealization X Q
    let G := ProEtale.finiteCoefficientComparison X Q
    let L := V.mapDerivedCategory.obj (P.origin n).L.obj
    have hL : DerivedCategory.TStructure.t.plus L := by
      obtain ⟨a, ha⟩ := (P.origin n).L.property
      let := ha
      exact ⟨a, V.isGE_mapDerivedCategory_obj (P.origin n).L.obj a⟩
    let c :
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q) Y).mapDerivedCategory ⋙
          U.mapDerivedCategory ≅ V.mapDerivedCategory ⋙ F.mapDerivedCategory :=
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Q) f) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm
    let a : G.mapDerivedCategory.obj L ≅ R.mapDerivedCategory.obj (M n) :=
      (Functor.mapDerivedCategoryCompIso F R).symm.app L ≪≫
        R.mapDerivedCategory.mapIso
          (c.symm.app (P.origin n).L.obj ≪≫ U.mapDerivedCategory.mapIso (P.alpha n))
    have hG : DerivedCategory.TStructure.t.plus (G.mapDerivedCategory.obj L) := by
      obtain ⟨b, hb⟩ := hL
      let := hb
      exact ⟨b, G.isGE_mapDerivedCategory_obj L b⟩
    let hM := DerivedCategory.TStructure.t.plus.prop_of_iso a hG
    exact ⟨hM, ⟨⟨⟨L, hL⟩, DerivedCategory.Plus.ι.preimageIso a⟩⟩⟩
  choose hM hW using origins
  apply compatibleOrigins_of_levelwise X d (H.obj K.obj) M hM
    (fun n ↦ Classical.choice (hW n))
  intro n
  let U := ProEtale.upperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) f
  let F := proEtaleRingModulePullback f ((pbcAdicRings Y d).obj (op n))
    ((pbcAdicRings X d).obj (op n)) (asIso (completedFiniteCoefficientMap f d n))
  let j : U ⋙ pbcFunctionRealization X d n ≅ pbcFunctionRealization Y d n ⋙ F :=
    (WeilConjectures.finitePullbackCoordinates f d n).choose
  let c : U.mapDerivedCategory ⋙ pbcDerivedFunctionRealization X d n ≅
      pbcDerivedFunctionRealization Y d n ⋙ F.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso j ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let h : d.pull f ≅ H := (pullbackDatumOrdinaryTransport f d).symm ≪≫ e
  have hF : F.mapDerivedCategory = d.finitePull f n := by
    apply congrArg (fun c ↦ (proEtaleRingModulePullback f
      ((pbcAdicRings Y d).obj (op n)) ((pbcAdicRings X d).obj (op n)) c).mapDerivedCategory)
    apply Iso.ext
    rfl
  exact c.app (P.K n) ≪≫ F.mapDerivedCategory.mapIso (eP n) ≪≫
    (eqToIso hF).app ((pbcCompletedReduction Y d n).obj K.obj) ≪≫
    (d.chi f n).app K.obj ≪≫ (pbcCompletedReduction X d n).mapIso (h.app K.obj)

/-- Transport preserves the specified integral full subcategory. -/
theorem pbcIsoAmbientPullback_preserves
    (K : PbcBoundedConstructibleComplete Y d) :
    PbcIsBoundedConstructibleComplete X d ((pbcIsoAmbientPullback f d).obj K.obj) := by
  let e := pbcIsoOrdinaryDerivedComparison f d
  refine ⟨?_, ?_, ?_⟩
  · exact pbcIsoAmbientPullback_preserves_intrinsic f d K
      (pbcIsoAmbientPullback f d) e
  · exact pbcIsoAmbientPullback_preserves_reductions f d K
      (pbcIsoAmbientPullback f d) e
  · exact pbcIsoAmbientPullback_preserves_origins f d K
      (pbcIsoAmbientPullback f d) e

include hf in
/-- The completed comparison is invertible on the integral complete objects. -/
@[instance] theorem pbcIsoCompletedComparison_isIso
    (K : PbcBoundedConstructibleComplete Y d) :
    IsIso (completedPullbackComparison f d K.obj) := by
  have hc : PbcIsIntrinsicallyComplete X d
      ((completedOrdinaryPullback f d).obj K.obj) :=
    pbcIsoAmbientPullback_preserves_intrinsic f d K (completedOrdinaryPullback f d)
      (Iso.refl _)
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let C := DerivedCategory.Q.objPreimage K.obj
  let eC := DerivedCategory.Q.objObjPreimageIso K.obj
  let P := DerivedCategory.Q.objPreimage ((completedOrdinaryPullback f d).obj K.obj)
  let eP := DerivedCategory.Q.objObjPreimageIso ((completedOrdinaryPullback f d).obj K.obj)
  have hK : IsDerivedCompleteIntrinsic Y d r a ha K.obj C eC :=
    (sfConstructibleCanonicalCompleteness Y d K.obj K.property.1).1 r a ha C eC
  obtain ⟨α, hα⟩ := completedPullback_isCompletion f d r a ha K.obj C eC hK P eP
  have hu : IsIso (intrinsicCompletionUnit X d r a ha
      ((completedOrdinaryPullback f d).obj K.obj) P eP) :=
    (sfConstructibleCanonicalCompleteness X d _ hc).1 r a ha P eP
  apply (isIso_comp_right_iff _ α.hom).mp
  rw [hα]
  infer_instance

/-- Completed pullback is the same coefficient transport, with its normalized comparison. -/
def pbcIsoCompletedPullback_identification (K : PbcBoundedConstructibleComplete Y d) :
    completedPullbackObject f d K.obj ≅ (pbcIsoAmbientPullback f d).obj K.obj :=
  (asIso (completedPullbackComparison f d K.obj)).symm ≪≫
    (pbcIsoOrdinaryDerivedComparison f d).app K.obj

/-- Restriction to the full subcategory, retaining all ambient derived morphisms. -/
def pbcIsoIntegralPullback :
    PbcBoundedConstructibleComplete Y d ⥤ PbcBoundedConstructibleComplete X d :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete X d)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y d) ⋙ pbcIsoAmbientPullback f d)
    (pbcIsoAmbientPullback_preserves f d)

attribute [local irreducible] pbcIsoIntegralPullback

/-- Coefficient transport is additive and linear for the original constant-section action. -/
theorem pbcIsoIntegralPullback_linear :
    (pbcIsoIntegralPullback f d).Additive ∧ (pbcIsoIntegralPullback f d).Linear A := by
  have hG : (proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))).Linear A := by
    constructor
    intro M N a b
    ext U x
    change (pbcCompletedSection X d ((proEtaleBaseChange f).op.obj U) b) •
        a.val.app ((proEtaleBaseChange f).op.obj U) x =
      ((completedCoefficientDirectImageMap f d).hom.app U
        (pbcCompletedSection Y d U b)) •
        a.val.app ((proEtaleBaseChange f).op.obj U) x
    rw [pbcCompletedSection_directImage]
  have hF : (pbcIsoModulePullback f d).Linear A :=
    (proEtaleRingModuleAdjunction f _ _ (asIso (completedCoefficientMap f d))).left_adjoint_linear
  constructor
  · unfold pbcIsoIntegralPullback
    infer_instance
  · constructor
    intro K L a b
    apply ObjectProperty.hom_ext
    unfold pbcIsoIntegralPullback
    exact (pbcIsoAmbientPullback f d).map_smul b a.hom

/-- Additivity supplied by the named coefficient-transport theorem. -/
instance pbcIsoIntegralPullback_additive : (pbcIsoIntegralPullback f d).Additive :=
  (pbcIsoIntegralPullback_linear f d).1

/-- Linearity supplied by the named constant-section compatibility theorem. -/
instance pbcIsoIntegralPullback_isLinear : (pbcIsoIntegralPullback f d).Linear A :=
  (pbcIsoIntegralPullback_linear f d).2

/-- On the raw rationalization transport sends a tensor a tensor u to a tensor P(u).
This construction retains precisely the original integral object representatives. -/
abbrev pbcRationalIsoPullback {T : Scheme.{u}} (e : Aut T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (p : A) :
    PbcRationalCategory T d p ⥤ PbcRationalCategory T d p :=
  ScalarLocalization.map A (PbcBoundedConstructibleComplete T d) p
    (pbcIsoIntegralPullback e.asIso.hom d)

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {T : Scheme.{u}} (e : Aut T)
  {E F : Padic.FiniteCoefficientFields l Ω}

omit hf in
private theorem scalarRightInverse
    {RA RB : Sheaf (ProEt.topology Y) RingCat.{u + 1}}
    {SA SB : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (ay : RA ⟶ RB) (ax : SA ⟶ SB)
    (aR : RA ⟶ (proEtaleSheafDirectImage f RingCat.{u + 1}).obj SA)
    (aS : RB ⟶ (proEtaleSheafDirectImage f RingCat.{u + 1}).obj SB)
    (h : ay ≫ aS = aR ≫ (proEtaleSheafDirectImage f RingCat.{u + 1}).map ax) :
    ∃! r : SheafOfModules.restrictScalars ax ⋙
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f) aR ≅
      SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f) aS ⋙
        SheafOfModules.restrictScalars ay,
      ∀ (N : SheafOfModules.{u + 1} SB) (U : Y.ProEtᵒᵖ)
        (x : N.val.obj ((proEtaleBaseChange f).op.obj U)),
        HEq ((r.hom.app N).val.app U x) x := by
  refine ⟨SheafOfModules.pushforwardCongr (F := proEtaleBaseChange f) h.symm, ?_, ?_⟩
  · intro N U x
    rfl
  · intro r' hr'
    apply Iso.ext
    ext N U x
    exact eq_of_heq (hr' N U x)

/-- Exact transport's right adjoints commute with restriction of coefficients.
The section equation fixes the comparison, not just its isomorphism class. -/
theorem pbcIsoScalarRightComparison_exists (h : E ≤ F) :
    ∃! r :
      pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.asIso.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω E))) ≅
        proEtaleRingModuleDirectImage e.asIso.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω F))) ⋙
          pbcRestrict (pbcCompletedScalarMap l Ω T h),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F)))
        (U : T.ProEtᵒᵖ) (x : ((pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.asIso.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω E)))).obj
            M).val.obj U),
        HEq ((r.hom.app M).val.app U x) x := by
  have hs :
      pbcActualCoefficientRingMap T (pbcCompletedScalarMap l Ω T h) ≫
          pbcActualStructureMap e.asIso.hom (pbcStageDatum.{u} l Ω F) =
        pbcActualStructureMap e.asIso.hom (pbcStageDatum.{u} l Ω E) ≫
          (proEtaleSheafDirectImage e.asIso.hom RingCat.{u + 1}).map
            (pbcActualCoefficientRingMap T (pbcCompletedScalarMap l Ω T h)) := by
    rw [pbcStageCoefficientMap_eq l Ω T h]
    exact pbcScalarCoefficientStructureSquare l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) e.asIso.hom
  exact scalarRightInverse e.asIso.hom
    (pbcActualCoefficientRingMap T (pbcCompletedScalarMap l Ω T h))
    (pbcActualCoefficientRingMap T (pbcCompletedScalarMap l Ω T h))
    (pbcActualStructureMap e.asIso.hom (pbcStageDatum.{u} l Ω E))
    (pbcActualStructureMap e.asIso.hom (pbcStageDatum.{u} l Ω F)) hs

/-- The right-adjoint comparison fixed by identity on sections. -/
def pbcIsoScalarRightComparison (h : E ≤ F) :
    pbcRestrict (pbcCompletedScalarMap l Ω T h) ⋙
          proEtaleRingModuleDirectImage e.asIso.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
            (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω E))) ≅
        proEtaleRingModuleDirectImage e.asIso.hom
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
            (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω F))) ⋙
          pbcRestrict (pbcCompletedScalarMap l Ω T h) :=
  (pbcIsoScalarRightComparison_exists l Ω e h).exists.choose

/-- The ordinary comparison is the mate of the sectionwise identity comparison.
This pins down its tensor normalization. -/
def pbcIsoOrdinaryScalarComparison (h : E ≤ F) :
    pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h) :=
  (conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction e.asIso.hom _ _
        (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω E)))).comp
      (pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h)))
    ((pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h)).comp
      (proEtaleRingModuleAdjunction e.asIso.hom _ _
        (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω F)))))).symm
    (pbcIsoScalarRightComparison l Ω e h)

/-- The ordinary comparison on nested complex functors, using the canonical
composition isomorphisms on both sides. -/
def pbcIsoOrdinaryComplexComparison (h : E ≤ F) :
    (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F)).mapHomologicalComplex
        (.up ℤ) ≅
      (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
        (.up ℤ) ⋙
        (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F))) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (pbcIsoOrdinaryScalarComparison l Ω e h) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T h))) (.up ℤ)).symm

attribute [local irreducible] pbcExtensionCounit pbcComplexCounit
  pbcIsoOrdinaryComplexComparison

private theorem isoTransportAmbientScalarComparison
    (T' : Scheme.{u}) (f' : T' ⟶ T') [IsIso f']
    {A' B' : Type (u + 1)} [CommRing A'] [CommRing B']
    (dA : AdicCoefficientDatum A') (dB : AdicCoefficientDatum B')
    (φ : pbcAdicCompletion T' dA ⟶ pbcAdicCompletion T' dB)
    (τ : (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙
        (pbcIsoModulePullback f' dB).mapHomologicalComplex (.up ℤ) ≅
      (pbcIsoModulePullback f' dA).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend φ).mapHomologicalComplex (.up ℤ)) :
    ∃! c : pbcDerivedExtend φ ⋙ pbcIsoAmbientPullback f' dB ≅
        pbcIsoAmbientPullback f' dA ⋙ pbcDerivedExtend φ,
      ∀ P : CochainComplex (pbcModules T' (pbcAdicCompletion T' dA)) ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcDerivedExtend φ).map
            ((pbcIsoModulePullback f' dA).mapDerivedCategoryFactors.hom.app P) ≫
          pbcComplexCounit φ
            (((pbcIsoModulePullback f' dA).mapHomologicalComplex (.up ℤ)).obj P) =
        (pbcIsoAmbientPullback f' dB).map (pbcComplexCounit φ P) ≫
          (pbcIsoModulePullback f' dB).mapDerivedCategoryFactors.hom.app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (τ.hom.app P) := by
  have hc := isoTransportCochainSquare
    (hG := pbcExtend_additive φ)
    (hFA := inferInstanceAs (pbcIsoModulePullback f' dA).Additive)
    (hFB := inferInstanceAs (pbcIsoModulePullback f' dB).Additive)
    (hEA := pbcIsoModulePullback_isEquivalence f' dA)
    (hEB := pbcIsoModulePullback_isEquivalence f' dB)
    (pbcExtend φ) (pbcDerivedExtend φ)
    (pbcExtensionCounit φ) (pbcDerivedExtension_universal φ)
    (pbcIsoModulePullback f' dA) (pbcIsoModulePullback f' dB) τ
  simpa only [isoTransportComplexCounitEq] using hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem pbcIsoAmbientScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcAmbientScalarExtension l Ω T h ⋙
        pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h,
      ∀ P : CochainComplex
          (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ,
        c.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcAmbientScalarExtension l Ω T h).map
            ((pbcIsoModulePullback e.asIso.hom
              (pbcStageDatum.{u} l Ω E)).mapDerivedCategoryFactors.hom.app P) ≫
          pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
            (((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
              (.up ℤ)).obj P) =
        (pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω F)).map
            (pbcComplexCounit (pbcCompletedScalarMap l Ω T h) P) ≫
          (pbcIsoModulePullback e.asIso.hom
            (pbcStageDatum.{u} l Ω F)).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((pbcIsoOrdinaryComplexComparison l Ω e h).hom.app P) := by
  exact isoTransportAmbientScalarComparison T e.asIso.hom
    (pbcStageDatum.{u} l Ω E) (pbcStageDatum.{u} l Ω F)
    (pbcCompletedScalarMap l Ω T h) (pbcIsoOrdinaryComplexComparison l Ω e h)

/-- The ambient Frobenius/scalar comparison with its representative normalization. -/
def pbcIsoAmbientScalarComparison (h : E ≤ F) :
    pbcAmbientScalarExtension l Ω T h ⋙
        pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω T h :=
  (pbcIsoAmbientScalarComparison_exists l Ω e h).exists.choose

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

section
attribute [local semireducible] pbcIsoIntegralPullback

/-- Fullness restricts the normalized ambient comparison uniquely. -/
theorem pbcIsoIntegralScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h,
      Functor.whiskerRight c.hom
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))) =
        Functor.whiskerLeft
          (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)))
          (pbcIsoAmbientScalarComparison l Ω e h).hom := by
  let c := pbcIsoAmbientScalarComparison l Ω e h
  let b : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (c.app K.obj))
      (fun a ↦ ObjectProperty.hom_ext _ (c.hom.naturality a.hom))
  refine ⟨b, rfl, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun t ↦ t.app K) hb'

end

/-- The integral comparison retaining its ambient normalization. -/
def pbcIsoIntegralScalarComparison (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω F) ≅
      pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcIntegralScalarExtension l Ω T hdim hl h :=
  (pbcIsoIntegralScalarComparison_exists l Ω e hdim hl h).exists.choose

set_option linter.unusedSectionVars false in
/-- Integral localization commutes with the explicitly linear coefficient transport. -/
theorem pbcIsoRationalization (E : Padic.FiniteCoefficientFields l Ω) :
    pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) =
      pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E) ⋙
        pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) := by
  refine CategoryTheory.Functor.ext
    (F := pbcRationalization T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E) ⋙
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E))
    (fun _ ↦ rfl) ?_
  intro K L a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact LinearMap.baseChange_tmul _ _ _

/-- The rational comparison is fixed on every original integral object. -/
theorem pbcIsoRationalScalarComparison_exists (h : E ≤ F) :
    ∃! c : pbcScalarExtension l Ω T hdim hl h ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F) ≅
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcScalarExtension l Ω T hdim hl h,
      ∀ K : PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E),
        c.hom.app
            ((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).obj K) =
          (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F)).map
            ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
          (eqToIso (pbcIsoRationalization l Ω e F)).hom.app
            ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
          (pbcRationalization T (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F)).map
            ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω T hdim hl h).inv.app
            ((pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj K) ≫
          (pbcScalarExtension l Ω T hdim hl h).map
            ((eqToIso (pbcIsoRationalization l Ω e E)).inv.app K) := by
  let QE := pbcStageLocalization l Ω T E
  let QF := pbcStageLocalization l Ω T F
  let SEF := pbcScalarExtension l Ω T hdim hl h
  let IEF := pbcIntegralScalarExtension l Ω T hdim hl h
  let PE := pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E)
    (pbcStageUniformizer.{u} l Ω E)
  let PF := pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F)
    (pbcStageUniformizer.{u} l Ω F)
  let IE := pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)
  let IF := pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω F)
  let a : QE ⋙ (SEF ⋙ PF) ≅ QE ⋙ (PE ⋙ SEF) :=
    (Functor.associator QE SEF PF).symm ≪≫
      Functor.isoWhiskerRight (pbcScalarIntegralComparison l Ω T hdim hl h) PF ≪≫
      Functor.associator IEF QF PF ≪≫
      Functor.isoWhiskerLeft IEF (eqToIso (pbcIsoRationalization l Ω e F)) ≪≫
      (Functor.associator IEF IF QF).symm ≪≫
      Functor.isoWhiskerRight (pbcIsoIntegralScalarComparison l Ω e hdim hl h) QF ≪≫
      Functor.associator IE IEF QF ≪≫
      Functor.isoWhiskerLeft IE (pbcScalarIntegralComparison l Ω T hdim hl h).symm ≪≫
      (Functor.associator IE QE SEF).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (pbcIsoRationalization l Ω e E)).symm SEF ≪≫
      Functor.associator QE PE SEF
  let W := pbcStageDenominators l Ω T hdim hl E
  have : QE.IsLocalization W := pbcStageLocalization_isLocalization l Ω T hdim hl E
  let FF := Localization.fullyFaithfulWhiskeringLeft QE W
    (PbcRationalCategory T (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F))
  let c : SEF ⋙ PF ≅ PE ⋙ SEF := FF.preimageIso a
  have hc : Functor.whiskerLeft QE c.hom = a.hom := FF.map_preimage a.hom
  have hnorm (K : PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) :
      c.hom.app (QE.obj K) =
        PF.map ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
          (eqToIso (pbcIsoRationalization l Ω e F)).hom.app (IEF.obj K) ≫
          QF.map ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω T hdim hl h).inv.app (IE.obj K) ≫
          SEF.map ((eqToIso (pbcIsoRationalization l Ω e E)).inv.app K) := by
    rw [show c.hom.app (QE.obj K) = a.hom.app K from congrArg (fun t ↦ t.app K) hc]
    simp only [a, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    dsimp only [Functor.comp_obj]
    simp only [Category.id_comp]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.comp_id]
    erw [Category.id_comp, Category.id_comp]
  refine ⟨c, hnorm, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨K⟩ := K
  exact (hc' K).trans (hnorm K).symm

/-- The Frobenius/scalar comparison determined by canonical tensor transport. -/
def pbcIsoRationalScalarComparison (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F) (pbcStageUniformizer.{u} l Ω F) ≅
      pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E) ⋙
        pbcScalarExtension l Ω T hdim hl h :=
  (pbcIsoRationalScalarComparison_exists l Ω e hdim hl h).exists.choose

end AlgebraicGeometry.Scheme
