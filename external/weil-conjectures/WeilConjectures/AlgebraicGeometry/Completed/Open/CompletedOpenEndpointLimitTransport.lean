/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
import all WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Basic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import all WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # Transport of normalized completed open endpoints

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-exchange and final
inverse-limit paragraphs (blueprint: lem-cbc-completed-open-endpoint-limit-transport).

All towers are derived objects of the category of strict module sequences. The
constant and completed coefficient rings remain distinct. The limit comparison
is the constant-diagram mate: its augmentation normalization uniquely fixes it,
and identifies it with the signed Roos / K-injective comparison of
`exactProductFunctorStrictLimit`. No comparison is chosen from a triangle alone.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t uC vC uD vD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] WeilConjectures.sfAbBijective
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Finite limits of strict diagrams are computed at each level.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
instance cbcEndpointWhiskerLimits {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [HasFiniteLimits C]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Finite colimits of strict diagrams are computed at each level.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
instance cbcEndpointWhiskerColimits {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [HasFiniteColimits C]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The existing exact ringed extension by zero, with its universal open adjunction.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
abbrev cbcEndpointOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  proEtaleRingOpenExtension j (d.completedRing T) (d.completedRing U) (d.integralRingIso j)

/-- The ordinary section-normalized open adjunction.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcEndpointOpen d j ⊣ proEtaleRingModulePullback j (d.completedRing T)
      (d.completedRing U) (d.integralRingIso j) := Adjunction.ofIsRightAdjoint _

/-- The exact derived open adjunction, using the published derived pullback.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointDerivedOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    (cbcEndpointOpen d j).mapDerivedCategory ⊣ d.pull j :=
  Adjunction.ofNatIsoRight (cbcEndpointOpenAdj d j).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).rightDerivedFunctorIsoMapDerivedCategory

/-- The open adjunction on actual derived strict towers.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointTowerOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcTowerDerived (cbcEndpointOpen d j) ⊣ d.towerPull j :=
  Adjunction.ofNatIsoRight
    ((cbcEndpointOpenAdj d j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (d.towerModulePull j).rightDerivedFunctorIsoMapDerivedCategory

attribute [local irreducible] cbcEndpointOpenAdj
  ProEtale.StrictTower.moduleJAdj exchangeOrdinaryResPull

private theorem cbcEndpointInverseMate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {LT : E ⥤ F} {RT : F ⥤ E}
    (a : L ⊣ R) (b : LT ⊣ RT) (P : C ⥤ E) (Q : D ⥤ F)
    (s : R ⋙ P ⟶ Q ⋙ RT) (K : C) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ s)).app K =
      (b.homEquiv _ _).symm (P.map (a.unit.app K) ≫ s.app (L.obj K)) := by
  apply (b.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ s) K).symm

/-- The inverse quotient/open comparison is the transpose of the reduced open unit.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointReductionInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (cbcTowerDerived (cbcEndpointOpen d j)).obj ((completedReductionTower U d).obj K) ⟶
      (completedReductionTower T d).obj ((cbcEndpointOpen d j).mapDerivedCategory.obj K) :=
  ((cbcEndpointTowerOpenAdj d j).homEquiv _ _).symm
    ((completedReductionTower U d).map ((cbcEndpointDerivedOpenAdj d j).unit.app K) ≫
      (d.reductionTowerPullbackIso j).inv.app ((cbcEndpointOpen d j).mapDerivedCategory.obj K))

private theorem cbcEndpointReduction_naturality {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K L : d.derived U) (k : K ⟶ L) :
    (cbcTowerDerived (cbcEndpointOpen d j)).map ((completedReductionTower U d).map k) ≫
        cbcEndpointReductionInv d j L =
      cbcEndpointReductionInv d j K ≫ (completedReductionTower T d).map
        ((cbcEndpointOpen d j).mapDerivedCategory.map k) := by
  let n := ((mateEquiv (cbcEndpointDerivedOpenAdj d j) (cbcEndpointTowerOpenAdj d j)).symm
    (TwoSquare.mk _ _ _ _ (d.reductionTowerPullbackIso j).inv))
  have h (M : d.derived U) : n.app M = cbcEndpointReductionInv d j M :=
    cbcEndpointInverseMate_app (cbcEndpointDerivedOpenAdj d j) (cbcEndpointTowerOpenAdj d j)
      (completedReductionTower U d) (completedReductionTower T d)
      (d.reductionTowerPullbackIso j).inv M
  have hn := n.naturality k
  simpa only [Functor.comp_map, h] using hn

private theorem cbcEndpointExactAdjunction_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = exactLocalizationDerivedAdjunction a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  let K' := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hs : (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K'
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Q.obj K) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K') = _ at hu
    erw [reassoc_of% hu]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj K')
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [reassoc_of% hf, Iso.inv_hom_id_app, Category.comp_id]
  have he : (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    rw [CategoryTheory.exact_unit_app]
    have hl := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom L K
    have hr := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom R
      ((L.mapHomologicalComplex (.up ℤ)).obj K)
    change L.mapDerivedCategoryFactorsh.hom.app K' = _ at hl
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K') = _ at hr
    rw [hl, hr]
    simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K))
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl
  exact (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K'))).mp
    (by simpa only [Category.assoc] using hs.trans he.symm)

private theorem cbcEndpointExact_unit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) [IsIso a.unit] :
    IsIso (exactLocalizationDerivedAdjunction a).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let P := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have h (P : CochainComplex C ℤ) :
      IsIso ((exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj P)) := by
    rw [CategoryTheory.exact_unit_app]
    have : IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hc (q : ℤ) :
          IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app P).f q) := by
        simp only [Adjunction.mapHomologicalComplex_unit_app_f]
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have := h P
  have hn := (exactLocalizationDerivedAdjunction a).unit.naturality e.hom
  dsimp only [Functor.id_map] at hn
  have : IsIso (e.hom ≫ (exactLocalizationDerivedAdjunction a).unit.app X) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

private theorem cbcEndpointOpen_fullFaithful {U T : Scheme.{t}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    (cbcEndpointOpen d j).Full ∧ (cbcEndpointOpen d j).Faithful := by
  obtain ⟨e, ⟨i⟩⟩ := proEtaleOpen_slicePresentation j
    (d.completedRing T) (d.completedRing U) (d.integralRingIso j)
  let := SheafOfModules.localizedUnit_isIso j (d.completedRing T)
  let ff := (SheafOfModules.localizedModuleAdjunctionIndependent
    (d.completedRing T) (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact ⟨Functor.Full.of_iso i.symm, Functor.Faithful.of_iso i.symm⟩

private theorem cbcEndpointReduction_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (K : d.derived U) : IsIso (cbcEndpointReductionInv d j K) := by
  let a := cbcEndpointOpenAdj d j
  let b := cbcEndpointTowerOpenAdj d j
  obtain ⟨hfull, hfaith⟩ := cbcEndpointOpen_fullFaithful d j
  have : IsIso a.unit := inferInstance
  have hu := cbcEndpointExact_unit_isIso a
  have : IsIso (cbcEndpointDerivedOpenAdj d j).unit := by
    dsimp only [cbcEndpointDerivedOpenAdj]
    rw [cbcEndpointExactAdjunction_eq]
    exact hu
  let H := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcEndpointOpen d j)
  have : H.Full := inferInstance
  have : H.Faithful := inferInstance
  have : IsIso (a.whiskerRight ℕᵒᵖ).unit := inferInstance
  have hub := cbcEndpointExact_unit_isIso (a.whiskerRight ℕᵒᵖ)
  have : IsIso b.unit := by
    dsimp only [b, cbcEndpointTowerOpenAdj]
    rw [cbcEndpointExactAdjunction_eq]
    exact hub
  have hfullb := b.fullyFaithfulLOfIsIsoUnit
  have := hfullb.full
  have := hfullb.faithful
  let ag := Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
    (@asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)).symm
  let e := a.leftAdjointUniq ag
  have := cbcOpenShriek_additive d j inferInstance
  have := cbcOpenShriek_finiteLimits d j inferInstance
  have := cbcOpenShriek_finiteColimits d j inferInstance
  let ed := Functor.mapDerivedCategoryNatIso e
  let et := Functor.mapDerivedCategoryNatIso
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e)
  let W := cbcOpenObject j inferInstance
  have : IsOpenImmersion W.hom := ‹IsOpenImmersion j›
  let rho := (cbcRingedOpenStrictReduction W d).exists.choose
  let k : (cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d ≅
      completedReductionTower U d ⋙ cbcTowerDerived (cbcEndpointOpen d j) :=
    Functor.isoWhiskerRight ed (completedReductionTower T d) ≪≫ rho ≪≫
      Functor.isoWhiskerLeft (completedReductionTower U d) et.symm
  have hc : IsIso (b.counit.app ((completedReductionTower T d).obj
      ((cbcEndpointOpen d j).mapDerivedCategory.obj K))) :=
    b.isIso_counit_app_iff_mem_essImage.mpr
      (Functor.essImage.ofIso (k.symm.app K) (Functor.obj_mem_essImage _ _))
  have : IsIso (b.counit.app ((completedReductionTower T d).obj
      ((cbcEndpointOpen d j).mapDerivedCategory.obj K))) := hc
  let n := ((mateEquiv (cbcEndpointDerivedOpenAdj d j) b).symm
    (TwoSquare.mk _ _ _ _ (d.reductionTowerPullbackIso j).inv))
  have hn : n.app K = cbcEndpointReductionInv d j K :=
    cbcEndpointInverseMate_app _ _ _ _ _ K
  rw [← hn]
  dsimp only [n]
  simp only [mateEquiv_symm_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp, TwoSquare.mk]
  erw [(cbcTowerDerived (cbcEndpointOpen d j)).map_id,
    (cbcTowerDerived (cbcEndpointOpen d j)).map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]
  have : IsIso ((cbcTowerDerived (cbcEndpointOpen d j)).map
      ((completedReductionTower U d).map ((cbcEndpointDerivedOpenAdj d j).unit.app K))) :=
    inferInstance
  have : IsIso ((cbcTowerDerived (cbcEndpointOpen d j)).map
      ((d.reductionTowerPullbackIso j).inv.app
        ((cbcEndpointOpen d j).mapDerivedCategory.obj K))) := inferInstance
  infer_instance

/-- The canonical quotient/open comparison is invertible and natural before evaluation.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: Use the exact open adjunction and the canonical reduction/pullback
comparison of def-weil-pbc-completed-pullback. On a K-flat representative the
transpose is the tensor balancing map from open extension of its reduction to
reduction of its open extension. The inverse is the usual balanced section map.
Open extension preserves K-flatness: tensoring with an acyclic ambient complex
is extension of tensor with its exact restriction. The maps commute with quotient
transitions, differentials and quotient augmentations. They therefore give inverse
strict tower maps and descend through quasi-isomorphisms. Naturality follows from
the open unit and the normalized reduction/pullback comparison, without faithfulness
of derived evaluation. -/
theorem cbcEndpointReductionInv_properties {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (∀ K : d.derived U, IsIso (cbcEndpointReductionInv d j K)) ∧
      ∀ (K L : d.derived U) (k : K ⟶ L),
        (cbcTowerDerived (cbcEndpointOpen d j)).map ((completedReductionTower U d).map k) ≫
            cbcEndpointReductionInv d j L =
          cbcEndpointReductionInv d j K ≫ (completedReductionTower T d).map
            ((cbcEndpointOpen d j).mapDerivedCategory.map k) := by
  exact ⟨cbcEndpointReduction_isIso d j, cbcEndpointReduction_naturality d j⟩

section Limit
variable {T S : Scheme.{t}}
  {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
  {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}

end Limit

end AlgebraicGeometry.Scheme
