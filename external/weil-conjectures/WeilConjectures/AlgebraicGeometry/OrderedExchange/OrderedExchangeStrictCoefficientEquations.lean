/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeTowerExchange

/-! # strictCoefficientEquations

## References

* Stacks 099M, 0D6D, 0D6E
* Stacks Tags 099M, 099N, 0A07 and 0E48

## Implementation details

`rho_pull_generic` is stated for abstract exact functors and derived reduction models, and
`rho_reductionTowerPullbackIso` is its instance at the strict pro-étale towers, so that the
kernel never unfolds the concrete derived-category instances.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

section DerivedSquares

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄]

/-- The derived square induced by an isomorphism of exact composites, evaluated on the
localization of a complex. -/
private theorem mapDerivedCategorySquareIso_hom_app_Q
    {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ C₄} {G₁ : C₁ ⥤ C₃} {G₂ : C₃ ⥤ C₄}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app K) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj K) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hG := Functor.mapDerivedCategoryCompIso_fac G₁ G₂ K
  have hF := Functor.mapDerivedCategoryCompIso_fac F₁ F₂ K
  have hN := Functor.mapDerivedCategoryNatIso_fac e K
  have hcF : (Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app K =
      𝟙 _ := by
    ext i
    rfl
  have hcG : (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).hom.app K =
      𝟙 _ := by
    ext i
    rfl
  rw [hcF] at hF
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hF
  rw [hcG] at hG
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hG
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [hG, hN, ← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The universal counit of a derived reduction model is natural in chain maps. -/
private theorem complexCounit_naturality {B C : Type*} [Category B] [Abelian B]
    [Category C] [Abelian C] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : B ⥤ C} [F.Additive] {P : CochainComplex B ℤ → Prop}
    (D : DerivedReductionModelData F P) {K K' : CochainComplex B ℤ} (φ : K ⟶ K') :
    D.reduction.map (DerivedCategory.Q.map φ) ≫ D.complexCounit K' =
      D.complexCounit K ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map φ) := by
  have h1 := (DerivedCategory.quotientCompQhIso B).inv.naturality φ
  have h2 := D.counit.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map φ)
  have h3 := (F.mapHomotopyCategoryFactors (.up ℤ)).hom.naturality φ
  have h4 := (DerivedCategory.quotientCompQhIso C).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map φ)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at h1 h2 h3 h4
  unfold DerivedReductionModelData.complexCounit
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% h2,
    ← Functor.map_comp_assoc, h3, Functor.map_comp_assoc, h4]
  simp only [Category.assoc]

end DerivedSquares

section OrdinaryPull

/-- The ordinary constant augmentation followed by `ordinaryRho` is the restricted completed
quotient unit, at every level. -/
theorem ordinaryAugmentation_ordinaryRho (T : Scheme.{t})
    (N : reductionModules T (d.completedRing T)) (n : ℕ) :
    ((ordinaryAugmentation d T).app ((reductionRestrict T (exchangeScalar d T)).obj N)).app
        (op n) ≫ ((ordinaryRho d T).hom.app N).app (op n) =
      (reductionRestrict T (exchangeScalar d T)).map
        (((completedReductionModuleUnit d T).app N).app (op n)) := by
  ext U x
  change (((ordinaryRho d T).hom.app N).app (op n)).val.app U
      ((((ordinaryAugmentation d T).app
        ((reductionRestrict T (exchangeScalar d T)).obj N)).app (op n)).val.app U x) =
    (((completedReductionModuleUnit d T).app N).app (op n)).val.app U x
  have h1 : ((((ordinaryAugmentation d T).app
      ((reductionRestrict T (exchangeScalar d T)).obj N)).app (op n)).val.app U x) =
      reductionTensorSection T (quotient d T n)
        ((reductionRestrict T (exchangeScalar d T)).obj N) U 1 x :=
    (ordinaryAugmentation_existsUnique d T).exists.choose_spec _ n U x
  have h2 := (completedReductionModuleUnit_exists d T).exists.choose_spec N n U x
  rw [h1]
  exact ((ordinaryRho_existsUnique d T).exists.choose_spec N n U 1 x).trans h2.symm

theorem ordinaryAugmentation_eq_unit (T : Scheme.{t})
    (L : reductionModules T (exchangeConstantRing T A)) (n : ℕ) :
    ((ordinaryAugmentation d T).app L).app (op n) =
      (proEtaleRingExtensionAdjunction (quotient d T n)).unit.app L := by
  ext W x
  have h1 : (((ordinaryAugmentation d T).app L).app (op n)).val.app W x =
      reductionTensorSection T (quotient d T n) L W 1 x :=
    (ordinaryAugmentation_existsUnique d T).exists.choose_spec L n W x
  rw [h1]
  exact ((pbcScalarAdjunction_exists (quotient d T n)).exists.choose_spec L W x).symm

/-- The ordinary constant reduction/pullback comparison preserves the ordinary augmentation. -/
theorem ordinaryAugmentation_ordinaryReductionPullIso {U V : Scheme.{t}} (u : U ⟶ V)
    (L : reductionModules V (exchangeConstantRing V A)) (n : ℕ) :
    (proEtaleRingModulePullback u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).map (((ordinaryAugmentation d V).app L).app (op n)) ≫
      ((ordinaryReductionPullIso d u).hom.app L).app (op n) =
    ((ordinaryAugmentation d U).app ((proEtaleRingModulePullback u (exchangeConstantRing V A)
        (exchangeConstantRing U A) (exchangeConstantIso u A)).obj L)).app (op n) := by
  rw [ordinaryAugmentation_eq_unit, ordinaryAugmentation_eq_unit]
  exact levelPullIso_unit d u n L

/-- The ordinary core of the compatibility of `rho` with pullback, at one tower level. -/
theorem ordinaryRho_pull {U V : Scheme.{t}} (u : U ⟶ V)
    (M : reductionModules V (d.completedRing V)) (n : ℕ) :
    (reductionRestrict U (exchangeScalar d U)).map
        (((stratumModuleReductionIso d u).hom.app M).app (op n)) ≫
      ((ordinaryRho d U).inv.app ((stratumModulePull d u).obj M)).app (op n) ≫
      ((reductionModule d U).map ((exchangeOrdinaryResPull d u).hom.app M)).app (op n) =
    (exchangeOrdinaryResPull d u).hom.app
        (((completedReductionModuleTowerFunctor V d).obj M).obj (op n)) ≫
      (proEtaleRingModulePullback u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).map (((ordinaryRho d V).inv.app M).app (op n)) ≫
      ((ordinaryReductionPullIso d u).hom.app
        ((reductionRestrict V (exchangeScalar d V)).obj M)).app (op n) := by
  have hε : Epi ((reductionRestrict U (exchangeScalar d U)).map
      ((stratumModulePull d u).map (((completedReductionModuleUnit d V).app M).app (op n)))) := by
    have := stratumModuleUnit_epi d V M n
    infer_instance
  apply (cancel_epi ((reductionRestrict U (exchangeScalar d U)).map
    ((stratumModulePull d u).map (((completedReductionModuleUnit d V).app M).app (op n))))).1
  have hs := congrArg (fun k ↦ k.app (op n))
    ((stratumModuleReductionIso_exists d u).exists.choose_spec M)
  dsimp only [NatTrans.comp_app] at hs
  have hc : ((d.constantPullbackIso u).hom.app M).app (op n) = 𝟙 _ := rfl
  erw [hc, Category.id_comp] at hs
  have hρU := ordinaryAugmentation_ordinaryRho d U ((stratumModulePull d u).obj M) n
  have hρV := ordinaryAugmentation_ordinaryRho d V M n
  have hρU' : (reductionRestrict U (exchangeScalar d U)).map
      (((completedReductionModuleUnit d U).app ((stratumModulePull d u).obj M)).app (op n)) ≫
      ((ordinaryRho d U).inv.app ((stratumModulePull d u).obj M)).app (op n) =
      ((ordinaryAugmentation d U).app ((reductionRestrict U (exchangeScalar d U)).obj
        ((stratumModulePull d u).obj M))).app (op n) := by
    rw [← hρU, Category.assoc, Iso.hom_inv_id_app_app]
    erw [Category.comp_id]
  have hρV' : (reductionRestrict V (exchangeScalar d V)).map
      (((completedReductionModuleUnit d V).app M).app (op n)) ≫
      ((ordinaryRho d V).inv.app M).app (op n) =
      ((ordinaryAugmentation d V).app ((reductionRestrict V (exchangeScalar d V)).obj M)).app
        (op n) := by
    rw [← hρV, Category.assoc, Iso.hom_inv_id_app_app]
    erw [Category.comp_id]
  have hA := congrArg (fun k ↦ k.app (op n))
    ((ordinaryAugmentation d U).naturality ((exchangeOrdinaryResPull d u).hom.app M))
  dsimp only [NatTrans.comp_app] at hA
  have hE := (exchangeOrdinaryResPull d u).hom.naturality
    (((completedReductionModuleUnit d V).app M).app (op n))
  dsimp only [Functor.comp_map] at hE
  have hO := ordinaryAugmentation_ordinaryReductionPullIso d u
    ((reductionRestrict V (exchangeScalar d V)).obj M) n
  rw [← Functor.map_comp_assoc]
  erw [hs]
  rw [reassoc_of% hρU']
  erw [← hA, reassoc_of% hE]
  rw [← Functor.map_comp_assoc]
  erw [hρV', hO]
  rfl

/-- The universal counit of the constant reduction is natural in chain maps. -/
theorem reductionComplexCounit_naturality (T : Scheme.{t})
    {K K' : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ} (φ : K ⟶ K') :
    (reduction d T).map (DerivedCategory.Q.map φ) ≫ reductionComplexCounit d T K' =
      reductionComplexCounit d T K ≫
        DerivedCategory.Q.map (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map φ) := by
  exact complexCounit_naturality (reductionData d T) φ

section DerivedPull

private theorem orderedAbSheafify' (T : Scheme.{t}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private theorem orderedAbLocallyBijective' (T : Scheme.{t}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T


private theorem scalarFlat (T : Scheme.{t}) :
    SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
      ((SheafOfModules.restrictScalars ((adicLisseForget T).map (exchangeScalar d T))).obj
        (SheafOfModules.unit ((adicLisseForget T).obj (d.completedRing T)))) := by
  let := d.noetherian
  have hc : ∀ n : ℕ, exchangeScalar d T ≫ (pbcCompletedComparison T d).inv ≫
      limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [exchangeScalar]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (adicDatumScalar_exists T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }).exists.choose_spec n
  exact (completed_constant_algebra_flat_quotients T d.ideal _
    (pbcCompletedComparison T d) (exchangeScalar d T) hc).1

/-- Pullback with the completed coefficient transport preserves flat-term K-flat complexes. -/
private theorem stratumPull_flatKFlat' {U V : Scheme.{t}} (u : U ⟶ V)
    (P : CochainComplex (reductionModules V (d.completedRing V)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology V)
        (R := d.completedRing V) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing U)
      (((stratumModulePull d u).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology U) (R := d.completedRing U)
      ((((stratumModulePull d u).mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists u (d.completedRing V)
  rcases I with ⟨r, ra, rm, rz, ro, L, e, ea, ez, es⟩
  dsimp only at hI
  subst L
  let I : SheafOfModules.AlgebraicInverseImage
      (proEtaleSheafInverseImage u (Type (t + 1))) (d.completedRing V)
      ((proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj (d.completedRing V)) :=
    ⟨r, ra, rm, rz, ro, proEtaleModuleInverseImage u (d.completedRing V), e, ea, ez, es⟩
  have : PreservesFiniteLimits (proEtaleSheafInverseImage u (Type (t + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage u (𝟙 V)).2.2.2.1
  have hobj (M) : (stratumModulePull d u).obj M =
      SheafOfModules.changeOfRings.{t, t + 1, t + 1}
        (d.integralRingIso u).hom (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (g : M ⟶ N), (stratumModulePull d u).map g =
      eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} (d.integralRingIso u).hom
          (I.modules.obj M) (I.modules.map g) ≫ eqToHom (hobj N).symm := by
    intro M N g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage u (Type (t + 1)))
    (proEtaleSheafDirectImage u (Type (t + 1)))
    (proEtaleSheafAdjunction u (Type (t + 1))) I (d.integralRingIso u).hom
    (stratumModulePull d u) hobj hmap P hP hflat

end DerivedPull

end OrdinaryPull

section GenericRhoPull

set_option linter.defProp false in
/-- The complex-level normalization of a comparison `ρ` between a derived reduction tower
followed by restriction and restriction followed by a derived reduction model, in the
shape of `RhoNormalization`, for abstract categories and functors. -/
def GenRhoNorm {B C T TC : Type*} [Category B] [Category C] [Category T] [Category TC]
    [Abelian B] [Abelian C] [Abelian T] [Abelian TC]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory T] [HasDerivedCategory TC]
    (R : B ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {red : C ⥤ TC} [red.Additive] {PC : CochainComplex C ℤ → Prop}
    (D : DerivedReductionModelData red PC) (RT : B ⥤ T) [RT.Additive]
    (tR : T ⥤ TC) [tR.Additive] [PreservesFiniteLimits tR] [PreservesFiniteColimits tR]
    (CR : DerivedCategory B ⥤ DerivedCategory T)
    (c : ∀ P : CochainComplex B ℤ, CR.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RT.mapHomologicalComplex (.up ℤ)).obj P))
    (oρ : R ⋙ red ≅ RT ⋙ tR) (ρ : CR ⋙ tR.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ D.reduction)
    (Q₁ Q₂ : CochainComplex B ℤ → Prop) : Prop :=
  ∀ P, Q₁ P → Q₂ P →
    ρ.hom.app (DerivedCategory.Q.obj P) ≫
        D.reduction.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        D.complexCounit ((R.mapHomologicalComplex (.up ℤ)).obj P) =
      tR.mapDerivedCategory.map (c P) ≫
        tR.mapDerivedCategoryFactors.hom.app ((RT.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oρ.symm (.up ℤ)).hom.app P)

set_option linter.unusedVariables false in
/-- The compatibility of a reduction comparison with pullback, for abstract exact functors
and derived reduction models. -/
theorem rho_pull_generic
    {BV BU CV CU TBV TBU TCV TCU : Type*}
    {iBV : Category BV} {iBU : Category BU} {iCV : Category CV} {iCU : Category CU}
    {iTBV : Category TBV} {iTBU : Category TBU} {iTCV : Category TCV} {iTCU : Category TCU}
    {aBV : Abelian BV} {aBU : Abelian BU} {aCV : Abelian CV} {aCU : Abelian CU}
    {aTBV : Abelian TBV} {aTBU : Abelian TBU} {aTCV : Abelian TCV} {aTCU : Abelian TCU}
    {hBV : HasDerivedCategory BV} {hBU : HasDerivedCategory BU}
    {hCV : HasDerivedCategory CV} {hCU : HasDerivedCategory CU}
    {hTBV : HasDerivedCategory TBV} {hTBU : HasDerivedCategory TBU}
    {hTCV : HasDerivedCategory TCV} {hTCU : HasDerivedCategory TCU}
    {pS : BV ⥤ BU} {pC : CV ⥤ CU} {rV : BV ⥤ CV} {rU : BU ⥤ CU}
    {tP : TBV ⥤ TBU} {tRV : TBV ⥤ TCV} {tRU : TBU ⥤ TCU} {tC : TCV ⥤ TCU}
    [pS.Additive] [PreservesFiniteLimits pS] [PreservesFiniteColimits pS]
    [pC.Additive] [PreservesFiniteLimits pC] [PreservesFiniteColimits pC]
    [rV.Additive] [PreservesFiniteLimits rV] [PreservesFiniteColimits rV]
    [rU.Additive] [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
    [tP.Additive] [PreservesFiniteLimits tP] [PreservesFiniteColimits tP]
    [tRV.Additive] [PreservesFiniteLimits tRV] [PreservesFiniteColimits tRV]
    [tRU.Additive] [PreservesFiniteLimits tRU] [PreservesFiniteColimits tRU]
    [tC.Additive] [PreservesFiniteLimits tC] [PreservesFiniteColimits tC]
    {RV : BV ⥤ TBV} {RU : BU ⥤ TBU} [RV.Additive] [RU.Additive]
    {redV : CV ⥤ TCV} {redU : CU ⥤ TCU} [redV.Additive] [redU.Additive]
    {PV : CochainComplex CV ℤ → Prop} {PU : CochainComplex CU ℤ → Prop}
    (DV : DerivedReductionModelData redV PV) (DU : DerivedReductionModelData redU PU)
    {CRV : DerivedCategory BV ⥤ DerivedCategory TBV}
    {CRU : DerivedCategory BU ⥤ DerivedCategory TBU}
    (cV : ∀ P : CochainComplex BV ℤ, CRV.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RV.mapHomologicalComplex (.up ℤ)).obj P))
    (cU : ∀ P : CochainComplex BU ℤ, CRU.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RU.mapHomologicalComplex (.up ℤ)).obj P))
    (oρV : rV ⋙ redV ≅ RV ⋙ tRV) (oρU : rU ⋙ redU ≅ RU ⋙ tRU)
    (ρV : CRV ⋙ tRV.mapDerivedCategory ≅ rV.mapDerivedCategory ⋙ DV.reduction)
    (ρU : CRU ⋙ tRU.mapDerivedCategory ≅ rU.mapDerivedCategory ⋙ DU.reduction)
    (eσ : RV ⋙ tP ≅ pS ⋙ RU)
    (σ : CRV ⋙ tP.mapDerivedCategory ≅ pS.mapDerivedCategory ⋙ CRU)
    (eα : pS ⋙ rU ≅ rV ⋙ pC) (eRP : tP ⋙ tRU ≅ tRV ⋙ tC) (eτ : redV ⋙ tC ≅ pC ⋙ redU)
    (τ : DV.reduction ⋙ tC.mapDerivedCategory ≅ pC.mapDerivedCategory ⋙ DU.reduction)
    {QV₁ QV₂ QS : CochainComplex BV ℤ → Prop} {QU₁ QU₂ : CochainComplex BU ℤ → Prop}
    (G : CochainComplex BV ℤ → Prop)
    (hres : ∀ M : DerivedCategory BV, ∃ L : CochainComplex BV ℤ, G L ∧
      Nonempty (DerivedCategory.Q.obj L ≅ M))
    (hgood : ∀ L, G L → QV₁ L ∧ QV₂ L ∧ QS L ∧ QU₁ ((pS.mapHomologicalComplex (.up ℤ)).obj L) ∧
      QU₂ ((pS.mapHomologicalComplex (.up ℤ)).obj L) ∧
      PV ((rV.mapHomologicalComplex (.up ℤ)).obj L) ∧
      PU ((pC.mapHomologicalComplex (.up ℤ)).obj ((rV.mapHomologicalComplex (.up ℤ)).obj L)))
    (hρV : GenRhoNorm rV DV RV tRV CRV cV oρV ρV QV₁ QV₂)
    (hρU : GenRhoNorm rU DU RU tRU CRU cU oρU ρU QU₁ QU₂)
    (hσ : ∀ L, QS L → DerivedReductionComparisonFormula pS tP RV RU CRV CRU cV cU eσ σ L)
    (hτ : ModelPullNormalized redV redU pC tC DV DU eτ τ)
    (hcore : ∀ N : BV, tRU.map (eσ.hom.app N) ≫ oρU.inv.app (pS.obj N) ≫
        redU.map (eα.hom.app N) =
      eRP.hom.app (RV.obj N) ≫ tC.map (oρV.inv.app N) ≫ eτ.hom.app (rV.obj N))
    (M : DerivedCategory BV) :
    tRU.mapDerivedCategory.map (σ.hom.app M) ≫ ρU.hom.app (pS.mapDerivedCategory.obj M) ≫
        DU.reduction.map ((Functor.mapDerivedCategorySquareIso eα).hom.app M) =
      (Functor.mapDerivedCategorySquareIso eRP).hom.app (CRV.obj M) ≫
        tC.mapDerivedCategory.map (ρV.hom.app M) ≫
        τ.hom.app (rV.mapDerivedCategory.obj M) := by
  unfold GenRhoNorm at hρV hρU
  unfold ModelPullNormalized at hτ
  obtain ⟨L, hL, ⟨e⟩⟩ := hres M
  have hg := hgood L hL
  have key : tRU.mapDerivedCategory.map (σ.hom.app (DerivedCategory.Q.obj L)) ≫
        ρU.hom.app (pS.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
        DU.reduction.map ((Functor.mapDerivedCategorySquareIso eα).hom.app
          (DerivedCategory.Q.obj L)) =
      (Functor.mapDerivedCategorySquareIso eRP).hom.app (CRV.obj (DerivedCategory.Q.obj L)) ≫
        tC.mapDerivedCategory.map (ρV.hom.app (DerivedCategory.Q.obj L)) ≫
        τ.hom.app (rV.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) := by
    have hi : IsIso (DU.complexCounit ((pC.mapHomologicalComplex (.up ℤ)).obj
        ((rV.mapHomologicalComplex (.up ℤ)).obj L))) := DU.complexCounit_isIso _ hg.2.2.2.2.2.2
    rw [← cancel_mono (DU.reduction.map (pC.mapDerivedCategory.map
        (rV.mapDerivedCategoryFactors.hom.app L)) ≫
      DU.reduction.map (pC.mapDerivedCategoryFactors.hom.app
        ((rV.mapHomologicalComplex (.up ℤ)).obj L)) ≫
      DU.complexCounit ((pC.mapHomologicalComplex (.up ℤ)).obj
        ((rV.mapHomologicalComplex (.up ℤ)).obj L)))]
    simp only [Category.assoc]
    -- left side
    have hα := mapDerivedCategorySquareIso_hom_app_Q eα L
    have e1 : DU.reduction.map ((Functor.mapDerivedCategorySquareIso eα).hom.app
          (DerivedCategory.Q.obj L)) ≫
        DU.reduction.map (pC.mapDerivedCategory.map (rV.mapDerivedCategoryFactors.hom.app L)) ≫
        DU.reduction.map (pC.mapDerivedCategoryFactors.hom.app
          ((rV.mapHomologicalComplex (.up ℤ)).obj L)) =
      DU.reduction.map (rU.mapDerivedCategory.map (pS.mapDerivedCategoryFactors.hom.app L)) ≫
        DU.reduction.map (rU.mapDerivedCategoryFactors.hom.app
          ((pS.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DU.reduction.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eα.hom (.up ℤ)).app L)) := by
      simp only [← Functor.map_comp, hα]
    rw [reassoc_of% e1]
    have n := ρU.hom.naturality (pS.mapDerivedCategoryFactors.hom.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj] at n
    rw [← reassoc_of% n]
    have c : DU.reduction.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eα.hom (.up ℤ)).app L)) ≫
        DU.complexCounit ((pC.mapHomologicalComplex (.up ℤ)).obj
          ((rV.mapHomologicalComplex (.up ℤ)).obj L)) =
      DU.complexCounit ((rU.mapHomologicalComplex (.up ℤ)).obj
          ((pS.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DerivedCategory.Q.map ((redU.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eα.hom (.up ℤ)).app L)) :=
      complexCounit_naturality DU _
    rw [c, reassoc_of% (hρU _ hg.2.2.2.1 hg.2.2.2.2.1)]
    have e2 : tRU.mapDerivedCategory.map (σ.hom.app (DerivedCategory.Q.obj L)) ≫
        tRU.mapDerivedCategory.map (CRU.map (pS.mapDerivedCategoryFactors.hom.app L)) ≫
        tRU.mapDerivedCategory.map (cU ((pS.mapHomologicalComplex (.up ℤ)).obj L)) =
      tRU.mapDerivedCategory.map (tP.mapDerivedCategory.map (cV L)) ≫
        tRU.mapDerivedCategory.map (tP.mapDerivedCategoryFactors.hom.app
          ((RV.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        tRU.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eσ.hom (.up ℤ)).app L)) := by
      have hσL := hσ L hg.2.2.1
      unfold DerivedReductionComparisonFormula at hσL
      simp only [← Functor.map_comp, hσL]
    rw [reassoc_of% e2]
    have t : tRU.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eσ.hom (.up ℤ)).app L)) ≫
        tRU.mapDerivedCategoryFactors.hom.app ((RU.mapHomologicalComplex (.up ℤ)).obj
          ((pS.mapHomologicalComplex (.up ℤ)).obj L)) =
      tRU.mapDerivedCategoryFactors.hom.app ((tP.mapHomologicalComplex (.up ℤ)).obj
          ((RV.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DerivedCategory.Q.map ((tRU.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eσ.hom (.up ℤ)).app L)) :=
      tRU.mapDerivedCategoryFactors.hom.naturality _
    rw [reassoc_of% t]
    -- right side
    have m := τ.hom.naturality (rV.mapDerivedCategoryFactors.hom.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj] at m
    rw [← reassoc_of% m, hτ _ hg.2.2.2.2.2.1]
    have e3 : tC.mapDerivedCategory.map (ρV.hom.app (DerivedCategory.Q.obj L)) ≫
        tC.mapDerivedCategory.map (DV.reduction.map (rV.mapDerivedCategoryFactors.hom.app L)) ≫
        tC.mapDerivedCategory.map (DV.complexCounit ((rV.mapHomologicalComplex (.up ℤ)).obj L)) =
      tC.mapDerivedCategory.map (tRV.mapDerivedCategory.map (cV L)) ≫
        tC.mapDerivedCategory.map (tRV.mapDerivedCategoryFactors.hom.app
          ((RV.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        tC.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex oρV.symm (.up ℤ)).hom.app L)) := by
      simp only [← Functor.map_comp, hρV L hg.1 hg.2.1]
    rw [reassoc_of% e3]
    have m1 := (Functor.mapDerivedCategorySquareIso eRP).hom.naturality (cV L)
    dsimp only [Functor.comp_map, Functor.comp_obj] at m1
    rw [← reassoc_of% m1]
    have tc : tC.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex oρV.symm (.up ℤ)).hom.app L)) ≫
        tC.mapDerivedCategoryFactors.hom.app ((redV.mapHomologicalComplex (.up ℤ)).obj
          ((rV.mapHomologicalComplex (.up ℤ)).obj L)) =
      tC.mapDerivedCategoryFactors.hom.app ((tRV.mapHomologicalComplex (.up ℤ)).obj
          ((RV.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DerivedCategory.Q.map ((tC.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex oρV.symm (.up ℤ)).hom.app L)) :=
      tC.mapDerivedCategoryFactors.hom.naturality _
    rw [reassoc_of% tc, reassoc_of% (mapDerivedCategorySquareIso_hom_app_Q eRP
      ((RV.mapHomologicalComplex (.up ℤ)).obj L))]
    have hQ : DerivedCategory.Q.map ((tRU.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eσ.hom (.up ℤ)).app L)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oρU.symm (.up ℤ)).hom.app
          ((pS.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DerivedCategory.Q.map ((redU.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eα.hom (.up ℤ)).app L)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex eRP.hom (.up ℤ)).app
          ((RV.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        DerivedCategory.Q.map ((tC.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex oρV.symm (.up ℤ)).hom.app L)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eτ (.up ℤ)).hom.app
          ((rV.mapHomologicalComplex (.up ℤ)).obj L)) := by
      simp only [← Functor.map_comp]
      congr 1
      ext i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f, NatIso.mapHomologicalComplex_hom_app_f, Iso.symm_hom]
      exact hcore (L.X i)
    rw [hQ]
  rw [← cancel_epi (tRU.mapDerivedCategory.map (tP.mapDerivedCategory.map (CRV.map e.hom)))]
  have n1 := σ.hom.naturality e.hom
  have n2 := ρU.hom.naturality (pS.mapDerivedCategory.map e.hom)
  have n3 := (Functor.mapDerivedCategorySquareIso eα).hom.naturality e.hom
  have m1 := (Functor.mapDerivedCategorySquareIso eRP).hom.naturality (CRV.map e.hom)
  have m2 := ρV.hom.naturality e.hom
  have m3 := τ.hom.naturality (rV.mapDerivedCategory.map e.hom)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 m1 m2 m3
  rw [← Functor.map_comp_assoc, n1, Functor.map_comp_assoc, reassoc_of% n2,
    ← Functor.map_comp, n3, Functor.map_comp, reassoc_of% key]
  rw [reassoc_of% m1, ← Functor.map_comp_assoc, m2, Functor.map_comp_assoc, m3]

end GenericRhoPull

/-- `ordinaryRho_pull` at all levels at once, as an equation of strict towers. -/
theorem ordinaryRho_pull_tower {U V : Scheme.{t}} (u : U ⟶ V)
    (N : reductionModules V (d.completedRing V)) :
    (exchangeTowerModuleRes d U).map ((stratumModuleReductionIso d u).hom.app N) ≫
        (ordinaryRho d U).inv.app ((stratumModulePull d u).obj N) ≫
        (reductionModule d U).map ((exchangeOrdinaryResPull d u).hom.app N) =
      (exchangeModuleResPull d u).hom.app ((completedReductionModuleTowerFunctor V d).obj N) ≫
        (exchangeTowerModulePull u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).map ((ordinaryRho d V).inv.app N) ≫
        (ordinaryReductionPullIso d u).hom.app
          ((reductionRestrict V (exchangeScalar d V)).obj N) := by
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app]
  exact ordinaryRho_pull d u N n.unop

/-- `RhoNormalization` of `rho`, in the generic shape used by `rho_pull_generic`. -/
theorem rhoNorm_gen (T : Scheme.{t}) :
    GenRhoNorm (reductionRestrict T (exchangeScalar d T)) (reductionData d T)
      (completedReductionModuleTowerFunctor T d) (exchangeTowerModuleRes d T)
      (completedReductionTower T d) (completedReductionTowerComplexCounit T d)
      (ordinaryRho d T) (rho d T)
      (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
        (R := d.completedRing T) P)
      (fun P ↦ ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
        (R := d.completedRing T) (P.X n)) :=
  (rho_existsUnique d T).exists.choose_spec

/-- Restriction of the strict reduction comparison `rho` is compatible with pullback. -/
theorem rho_reductionTowerPullbackIso {U V : Scheme.{t}} (u : U ⟶ V) (M : d.derived V) :
    (exchangeTowerRes d U).map ((d.reductionTowerPullbackIso u).hom.app M) ≫
        (rho d U).hom.app ((d.pull u).obj M) ≫
        (reduction d U).map ((alpha d u).hom.app M) =
      (exchangeResPull d u).hom.app ((completedReductionTower V d).obj M) ≫
        (exchangeConstantPull (A := A) u).map ((rho d V).hom.app M) ≫
        (reductionPullIso d u).hom.app ((res d V).obj M) := by
  exact rho_pull_generic (reductionData d V) (reductionData d U)
    (completedReductionTowerComplexCounit V d) (completedReductionTowerComplexCounit U d)
    (ordinaryRho d V) (ordinaryRho d U) (rho d V) (rho d U)
    (stratumModuleReductionIso d u) (d.reductionTowerPullbackIso u)
    (exchangeOrdinaryResPull d u) (exchangeModuleResPull d u) (ordinaryReductionPullIso d u)
    (reductionPullIso d u)
    (fun L ↦ L.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology V) (R := d.completedRing V) (L.X n))
    (fun M ↦ by
      obtain ⟨L, s, hL, hs⟩ :=
        flatKFlatResolution V (d.completedRing V) (DerivedCategory.Q.objPreimage M)
      exact ⟨L, hL, ⟨asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩)
    (fun L hL ↦ ⟨hL.1, hL.2, hL.1, (stratumPull_flatKFlat' d u L hL.1 hL.2).1,
      (stratumPull_flatKFlat' d u L hL.1 hL.2).2,
      (SheafOfModules.isKFlat_restrictScalars_of_flat (exchangeScalar d V) (scalarFlat d V)
        L hL.1).1,
      pullback_kFlat u _ _ (exchangeConstantIso u A) _
        (SheafOfModules.isKFlat_restrictScalars_of_flat (exchangeScalar d V) (scalarFlat d V)
          L hL.1).1
        ((SheafOfModules.isKFlat_restrictScalars_of_flat (exchangeScalar d V) (scalarFlat d V)
          L hL.1).2 hL.2)⟩)
    (rhoNorm_gen d V) (rhoNorm_gen d U)
    (completedReductionPullbackIso_existsUnique d u).choose_spec.1
    (reductionPullIso_existsUnique d u).choose_spec.1
    (ordinaryRho_pull_tower d u) M

/-- The adjunct of a whiskered mate: transposing `s.app M ≫ H.map t` under the second
adjunction is `G` applied to the transpose of `t`, followed by the mate. -/
private theorem mate_homEquiv
    {A' B' C' D' : Type*} [Category A'] [Category B'] [Category C'] [Category D']
    {L : A' ⥤ B'} {R : B' ⥤ A'} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : A' ⥤ C'} {H : B' ⥤ D'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A') (N : B') (t : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map t) =
      G.map (adj.homEquiv M N t) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

/-- The restriction/direct-image comparison of strict towers is the mate of the
restriction/pullback comparison, in adjunct form. -/
theorem exchangeResPush_homEquiv {U V : Scheme.{t}} (u : U ⟶ V)
    (Z : DerivedCategory (d.towers V)) (W : DerivedCategory (d.towers U))
    (x : (d.towerPull u).obj Z ⟶ W) :
    (exchangeTowerAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso u A)).homEquiv _ _
        ((exchangeResPull d u).inv.app Z ≫ (exchangeTowerRes d U).map x) =
      (exchangeTowerRes d V).map ((d.towerAdjunction u).homEquiv Z W x) ≫
        (exchangeResPush d u).hom.app W := by
  have heq := exactDerivedMate_eq (d.towerModuleAdjunction u)
    (exchangeTowerModuleAdjunction u (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso u A))
    (exchangeModuleResPull d u).symm (exchangeModuleResPush d u)
    (exchangeModuleResPull_mate d u) (exchangeResPush d u)
    (exchangeResPush_existsUnique d u).choose_spec.1
  rw [heq, exactDerivedMate]
  have hm := mate_homEquiv (d.towerAdjunction u)
    (exchangeTowerAdjunction u (exchangeConstantRing V A)
      (exchangeConstantRing U A) (exchangeConstantIso u A))
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom) Z W x
  have hs : (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom =
      (exchangeResPull d u).inv := by
    simp only [Functor.mapDerivedCategorySquareIso, exchangeResPull, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_symm]
  rw [hs] at hm ⊢
  exact hm

/-- Restriction of the integral derived counit is the constant derived counit, conjugated by
`alpha` and `chi`. -/
theorem res_counit {U V : Scheme.{t}} (u : U ⟶ V) (K : d.derived U) :
    (res d U).map ((proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
        (d.integralRingIso u)).counit.app K) =
      (alpha d u).hom.app ((d.push u).obj K) ≫ (pull (A := A) u).map ((chi d u).hom.app K) ≫
        (proEtaleRingDerivedAdjunction u (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso u A)).counit.app ((res d U).obj K) := by
  let aS := proEtaleRingDerivedAdjunction u (d.completedRing V) (d.completedRing U)
    (d.integralRingIso u)
  let aR := proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  have h := (proEtaleRingSheafChangeAdjunction u (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U) (exchangeScalar d V) (exchangeScalar d U)
    (exchangeConstantIso u A) (d.integralRingIso u) (exchangeScalar_comm d u)).2.2
      ((d.push u).obj K) K (aS.counit.app K)
  have h1 : aS.homEquiv ((d.push u).obj K) K (aS.counit.app K) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact aS.right_triangle_components K
  erw [h1] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h2 := congrArg (aR.homEquiv _ _).symm h
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h2
  have h3 : (alpha d u).inv.app ((d.push u).obj K) ≫ (res d U).map (aS.counit.app K) =
      (pull (A := A) u).map ((chi d u).hom.app K) ≫ aR.counit.app ((res d U).obj K) := h2
  calc (res d U).map (aS.counit.app K)
      = (alpha d u).hom.app ((d.push u).obj K) ≫
          ((alpha d u).inv.app ((d.push u).obj K) ≫ (res d U).map (aS.counit.app K)) := by
        rw [Iso.hom_inv_id_app_assoc]
    _ = _ := by rw [h3]

/-- Restriction of the strict reduction comparison `rho` is compatible with the strict
projection formula maps. -/
theorem rho_towerProjection {U V : Scheme.{t}} (u : U ⟶ V) (K : d.derived U) :
    (exchangeTowerRes d V).map (d.towerProjection u K) ≫
        (exchangeResPush d u).hom.app ((completedReductionTower U d).obj K) ≫
        (exchangeConstantPush (A := A) u).map ((rho d U).hom.app K) =
      (rho d V).hom.app ((d.push u).obj K) ≫
        (reduction d V).map ((chi d u).hom.app K) ≫
        projection d u ((res d U).obj K) := by
  have hP := rho_reductionTowerPullbackIso d u ((d.push u).obj K)
  have hc := res_counit d u K
  have hres := exchangeResPush_homEquiv d u
    ((completedReductionTower V d).obj ((d.push u).obj K)) ((completedReductionTower U d).obj K)
    ((d.reductionTowerPullbackIso u).hom.app ((d.push u).obj K) ≫
      (completedReductionTower U d).map ((proEtaleRingDerivedAdjunction u (d.completedRing V)
        (d.completedRing U) (d.integralRingIso u)).counit.app K))
  have hn := (rho d U).hom.naturality ((proEtaleRingDerivedAdjunction u (d.completedRing V)
    (d.completedRing U) (d.integralRingIso u)).counit.app K)
  have hR := (reductionPullIso d u).hom.naturality ((chi d u).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hR
  have hP' : (exchangeResPull d u).inv.app ((completedReductionTower V d).obj ((d.push u).obj K)) ≫
      (exchangeTowerRes d U).map ((d.reductionTowerPullbackIso u).hom.app ((d.push u).obj K)) ≫
      (rho d U).hom.app ((d.pull u).obj ((d.push u).obj K)) ≫
      (reduction d U).map ((alpha d u).hom.app ((d.push u).obj K)) =
    (exchangeConstantPull (A := A) u).map ((rho d V).hom.app ((d.push u).obj K)) ≫
      (reductionPullIso d u).hom.app ((res d V).obj ((d.push u).obj K)) := by
    rw [hP, Iso.inv_hom_id_app_assoc]
  unfold AdicCoefficientDatum.towerProjection projection
  rw [← reassoc_of% hres, ← Adjunction.homEquiv_naturality_right]
  erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  apply congrArg
  simp only [Functor.map_comp, Category.assoc]
  erw [hn]
  rw [hc]
  simp only [Functor.map_comp]
  rw [reassoc_of% hP']
  erw [reassoc_of% hR]

/-- The second strict coefficient equation: restriction of the strict realization `H`
followed by `beta` is `rhoM` followed by the constant `H`. -/
theorem exchangeRealizationH_beta (K : d.derived X) :
    (exchangeTowerRes d Y').map (exchangeRealizationH (f := f) (g := g) d K).hom ≫
        (beta (f := f) (g := g) d K).hom =
      (rhoM (f := f) (g := g) d K).hom ≫ (H (f := f) (g := g) d ((res d X).obj K)).hom := by
  let M := (d.push f).obj K
  have hP := rho_reductionTowerPullbackIso d g M
  have hQ := rho_towerProjection d f K
  have hP' : (exchangeResPull d g).hom.app ((completedReductionTower Y d).obj M) ≫
      (exchangeConstantPull (A := A) g).map ((rho d Y).hom.app M) =
    (exchangeTowerRes d Y').map ((d.reductionTowerPullbackIso g).hom.app M) ≫
      (rho d Y').hom.app ((d.pull g).obj M) ≫
      (reduction d Y').map ((alpha d g).hom.app M) ≫
      (reductionPullIso d g).inv.app ((res d Y).obj M) := by
    rw [reassoc_of% hP, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hN := (exchangeResPull d g).hom.naturality (d.towerProjection f K)
  have hR := (reductionPullIso d g).inv.naturality ((chi d f).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hN hR
  simp only [exchangeRealizationH, beta, rhoM, H, exchangeCornerB, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  rw [reassoc_of% hN]
  rw [← Functor.map_comp, ← Functor.map_comp, hQ]
  simp only [Functor.map_comp]
  rw [reassoc_of% hP', ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hR]

/-- The expanded form of `towerV'_delta`, after cancelling the strict projection `towerH`. -/
theorem towerV'_delta_expanded (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (exchangeTowerRes d Y').map ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
      (exchangeTowerRes d Y').map
        ((completedReductionTower Y' d).map ((d.integralExchange sq).app K)) ≫
      (exchangeTowerRes d Y').map (d.towerProjection f' ((d.pull g').obj K)) ≫
      (exchangeTowerRes d Y').map
        ((d.towerPush f').map ((d.reductionTowerPullbackIso g').inv.app K)) ≫
      (exchangeResPush d f').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPush (A := A) f').map
        ((exchangeResPull d g').hom.app ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPush (A := A) f').map
        ((exchangeConstantPull (A := A) g').map ((rho d X).hom.app K)) =
    (exchangeTowerRes d Y').map ((d.towerPull g).map (d.towerProjection f K)) ≫
      (exchangeResPull d g).hom.app ((d.towerPush f).obj ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPull (A := A) g).map
        ((exchangeResPush d f).hom.app ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPull (A := A) g).map
        ((exchangeConstantPush (A := A) f).map ((rho d X).hom.app K)) ≫
      (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
        ((reduction d X).obj ((res d X).obj K)) := by
  have hG := restriction_strictExchange d sq K
  have h1 := rho_reductionTowerPullbackIso d g ((d.push f).obj K)
  have h2 := rho_reductionTowerPullbackIso d g' K
  have h3 := rho_towerProjection d f K
  have h4 := rho_towerProjection d f' ((d.pull g').obj K)
  have hrho := (rho d Y').hom.naturality ((d.integralExchange sq).app K)
  have hN := (exchangeResPull d g).hom.naturality (d.towerProjection f K)
  have hE := (exchangeResPush d f').hom.naturality
    ((d.reductionTowerPullbackIso g').inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hrho hN hE
  have h1' : (exchangeResPull d g).hom.app ((completedReductionTower Y d).obj ((d.push f).obj K)) ≫
      (exchangeConstantPull (A := A) g).map ((rho d Y).hom.app ((d.push f).obj K)) =
    (exchangeTowerRes d Y').map ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
      (rho d Y').hom.app ((d.pull g).obj ((d.push f).obj K)) ≫
      (reduction d Y').map ((alpha d g).hom.app ((d.push f).obj K)) ≫
      (reductionPullIso d g).inv.app ((res d Y).obj ((d.push f).obj K)) := by
    rw [reassoc_of% h1, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have h2' : (exchangeTowerRes d X').map ((d.reductionTowerPullbackIso g').inv.app K) ≫
      (exchangeResPull d g').hom.app ((completedReductionTower X d).obj K) ≫
      (exchangeConstantPull (A := A) g').map ((rho d X).hom.app K) =
    (rho d X').hom.app ((d.pull g').obj K) ≫ (reduction d X').map ((alpha d g').hom.app K) ≫
      (reductionPullIso d g').inv.app ((res d X).obj K) := by
    rw [← cancel_epi ((exchangeTowerRes d X').map ((d.reductionTowerPullbackIso g').hom.app K)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [reassoc_of% h2, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have h3' := congrArg (exchangeConstantPull (A := A) g).map h3
  have h2'' := congrArg (exchangeConstantPush (A := A) f').map h2'
  simp only [Functor.map_comp] at h3' h2''
  have hL : (exchangeTowerRes d Y').map
        ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
      (exchangeTowerRes d Y').map
        ((completedReductionTower Y' d).map ((d.integralExchange sq).app K)) ≫
      (exchangeTowerRes d Y').map (d.towerProjection f' ((d.pull g').obj K)) ≫
      (exchangeTowerRes d Y').map
        ((d.towerPush f').map ((d.reductionTowerPullbackIso g').inv.app K)) ≫
      (exchangeResPush d f').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPush (A := A) f').map
        ((exchangeResPull d g').hom.app ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPush (A := A) f').map
        ((exchangeConstantPull (A := A) g').map ((rho d X).hom.app K)) =
      (exchangeTowerRes d Y').map
        ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
      (rho d Y').hom.app ((d.pull g).obj ((d.push f).obj K)) ≫
      (reduction d Y').map ((res d Y').map ((d.integralExchange sq).app K)) ≫
      (reduction d Y').map ((chi d f').hom.app ((d.pull g').obj K)) ≫
      projection d f' ((res d X').obj ((d.pull g').obj K)) ≫
      (exchangeConstantPush (A := A) f').map ((reduction d X').map ((alpha d g').hom.app K)) ≫
      (exchangeConstantPush (A := A) f').map
        ((reductionPullIso d g').inv.app ((res d X).obj K)) := by
    rw [reassoc_of% hE, h2'', reassoc_of% h4, reassoc_of% hrho]
  have hR : (exchangeTowerRes d Y').map ((d.towerPull g).map (d.towerProjection f K)) ≫
      (exchangeResPull d g).hom.app ((d.towerPush f).obj ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPull (A := A) g).map
        ((exchangeResPush d f).hom.app ((completedReductionTower X d).obj K)) ≫
      (exchangeConstantPull (A := A) g).map
        ((exchangeConstantPush (A := A) f).map ((rho d X).hom.app K)) =
      (exchangeTowerRes d Y').map
        ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K)) ≫
      (rho d Y').hom.app ((d.pull g).obj ((d.push f).obj K)) ≫
      (reduction d Y').map ((alpha d g).hom.app ((d.push f).obj K)) ≫
      (reductionPullIso d g).inv.app ((res d Y).obj ((d.push f).obj K)) ≫
      (exchangeConstantPull (A := A) g).map ((reduction d Y).map ((chi d f).hom.app K)) ≫
      (exchangeConstantPull (A := A) g).map (projection d f ((res d X).obj K)) := by
    rw [reassoc_of% hN, h3', reassoc_of% h1']
  rw [hL, reassoc_of% hR, hG]

/-- The third strict coefficient equation: restriction of the strict exchange `towerV'`
is the constant strict tower mate, conjugated by `beta` and `delta`. -/
theorem towerV'_delta (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (exchangeTowerRes d Y').map (d.towerV' sq K) ≫ (delta (f' := f') (g' := g') d K).hom =
      (beta (f := f) (g := g) d K).hom ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((reduction d X).obj ((res d X).obj K)) := by
  rw [← cancel_epi ((exchangeTowerRes d Y').map ((d.towerPull g).map (d.towerProjection f K)))]
  simp only [AdicCoefficientDatum.towerV', AdicCoefficientDatum.towerV,
    AdicCoefficientDatum.towerH, AdicCoefficientDatum.towerH', beta, delta, exchangeCornerB,
    exchangeCornerD, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, asIso_hom, asIso_inv, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp (d.towerPull g), IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact towerV'_delta_expanded d sq K

set_option linter.unusedVariables false in
/-- The tower map `towerV'` is the integral exchange conjugated by the realization isomorphisms
`H` and `H'`, and it is compatible with `rhoM`, `beta`, `delta` and the tower mate. -/
theorem strictCoefficientEquations (sq : ChosenCartesianSquare g' f' f g) :
    ∀ (K : d.derived X) (hK : d.TowerComplete X K),
      (d.towerV' sq K =
        (exchangeRealizationH (f := f) (g := g) d K).inv ≫
          (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
          (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom) ∧
      ((exchangeTowerRes d Y').map
          (exchangeRealizationH (f := f) (g := g) d K).hom ≫
            (beta (f := f) (g := g) d K).hom =
        (rhoM (f := f) (g := g) d K).hom ≫
          (H (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((exchangeTowerRes d Y').map (d.towerV' sq K) ≫
          (delta (f' := f') (g' := g') d K).hom =
        (beta (f := f) (g := g) d K).hom ≫
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
            ((reduction d X).obj ((res d X).obj K))) := by
  intro K _
  refine ⟨?_, exchangeRealizationH_beta d K, towerV'_delta d sq K⟩
  simp only [AdicCoefficientDatum.towerV', AdicCoefficientDatum.towerV,
    exchangeRealizationH, exchangeRealizationHPrime, AdicCoefficientDatum.towerH,
    AdicCoefficientDatum.towerH', Iso.trans_inv, Iso.trans_hom,
    Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.OrderedExchange
