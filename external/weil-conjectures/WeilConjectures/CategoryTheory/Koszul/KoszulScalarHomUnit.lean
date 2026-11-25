/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarFactorBasis
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomDiagram
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import all WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import all WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import all Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.Algebra.Homology.Monoidal.Dual

/-! # KoszulScalarHomUnit for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-hom-unit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

private theorem koszulEvaluation_unit (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (m : ℕᵒᵖ) :
    ringedKoszulTensorUnitComponent O r a N m ≫ (koszulEvaluation O r a N).hom.app m =
      (ringedHomUnitEvaluationIso O N).inv ≫
        ((homComplexFunctor (R := O)).map
          (ringedKoszulProjection O r a m.unop).op).app N := by
  change ringedKoszulTensorUnitComponent O r a N m ≫
    ringedComplexTensorEvaluation O ((ringedKoszulDiagram O r a).obj m.unop) N = _
  rw [ringedKoszulTensorUnitComponent, ringedKoszulDualUnit,
    ← ringedComplexHomUnit_eq O (ringedSiteRingComplex O), Functor.map_comp]
  simp only [Category.assoc]
  erw [ringedComplexTensorEvaluation_source O
    (ringedKoszulProjection O r a m.unop) N]
  have h := congrArg (fun f : N ⟶ homComplex (R := O) (ringedSiteRingComplex O) N ↦
    f ≫ ((homComplexFunctor (R := O)).map
      (ringedKoszulProjection O r a m.unop).op).app N)
    (ringedComplexTensorEvaluation_unit O N)
  rw [ringedComplexHomUnit_eq O N] at h
  simpa only [Category.assoc] using h

private theorem homUnitScalar_evaluation (φ : R ⟶ B) (N : ringedSiteComplex B) :
    (restrictComplex φ).map
        (((homComplexFunctor (R := B)).map (scalarTensorComparison φ).j.hom.op).app N) ≫
        ((SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta
          (ringedSiteRingComplex R) N).hom ≫
        (ringedHomUnitEvaluationIso R ((restrictComplex φ).obj N)).hom =
      (restrictComplex φ).map (ringedHomUnitEvaluationIso B N).hom := by
  let sR := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one R)
  let sB := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one B)
  have hjm : (extension φ).map sR.inv ≫ (scalarTensorComparison φ).j.hom.f 0 =
      (SheafOfModules.scalarExtensionUnitIso φ).hom ≫ sB.inv := by
    apply (cancel_mono sB.hom).mp
    have h := congrArg Iso.hom (scalarRankOne φ)
    simpa only [ScalarKoszulTransport.rankOneIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, HomologicalComplex.Hom.isoApp_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, sR, sB] using h
  have hj (U : Sᵒᵖ) : ((scalarTensorComparison φ).j.hom.f 0).val.app U
      (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ
        ((ringedSiteRingComplex R).X 0) U (1 : B.obj.obj U)
        (sR.inv.val.app U (1 : R.obj.obj U))) =
      sB.inv.val.app U (1 : B.obj.obj U) := by
    have h := congrArg (fun f ↦ f.val.app U
      (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ (one R) U
        (1 : B.obj.obj U) (1 : R.obj.obj U))) hjm
    change ((scalarTensorComparison φ).j.hom.f 0).val.app U
      ((SheafOfModules.changeOfRingsHomOfUniverses.{u, u, u, u} φ _ sR.inv).val.app U _) =
      sB.inv.val.app U ((SheafOfModules.scalarExtensionUnitIso φ).hom.val.app U _) at h
    simpa only [SheafOfModules.scalarExtension_map_tmul,
      SheafOfModules.scalarExtensionUnitIso_tmul, map_one, one_mul] using h
  apply HomologicalComplex.hom_ext
  intro n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change SheafOfModules.StrictScalarHom.evaluate _ _ n 0 n (zero_add n) U
      (((SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta
        (ringedSiteRingComplex R) N).hom.f n |>.val.app U
        (((((homComplexFunctor (R := B)).map
          (scalarTensorComparison φ).j.hom.op).app N).f n).val.app U g))
          (sR.inv.val.app U (1 : R.obj.obj U)) =
    SheafOfModules.StrictScalarHom.evaluate _ N n 0 n (zero_add n) U g
      (sB.inv.val.app U (1 : B.obj.obj U))
  rw [(SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta_evaluate]
  have h := homComplexFunctor_map_f_π (scalarTensorComparison φ).j.hom (𝟙 N)
    n 0 n (zero_add n)
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at h
  have he := congrArg (fun f ↦
    (((f.val.app U g).app (op (Over.mk (𝟙 U.unop)))).hom
      (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ
        ((ringedSiteRingComplex R).X 0) U (1 : B.obj.obj U)
        (sR.inv.val.app U (1 : R.obj.obj U))))) h
  exact he.trans (congrArg
    (SheafOfModules.StrictScalarHom.evaluate _ N n 0 n (zero_add n) U g) (hj U))

private theorem homUnitScalar (φ : R ⟶ B) (N : ringedSiteComplex B) :
    (restrictComplex φ).map (ringedHomUnitEvaluationIso B N).inv ≫
        (restrictComplex φ).map
          (((homComplexFunctor (R := B)).map (scalarTensorComparison φ).j.hom.op).app N) ≫
        ((SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta
          (ringedSiteRingComplex R) N).hom =
      (ringedHomUnitEvaluationIso R ((restrictComplex φ).obj N)).inv := by
  apply (cancel_mono (ringedHomUnitEvaluationIso R ((restrictComplex φ).obj N)).hom).mp
  rw [Category.assoc, Category.assoc, homUnitScalar_evaluation,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Iso.inv_hom_id]

/-- Compose a projection compatibility square with a normalized Hom-unit square.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-hom-unit). -/
theorem homUnitCompositionCore
    {D : Type*} [Category D] {D' : Type*} [Category D'] (F : D ⥤ D')
    {X U V W Z : D} {T Y : D'}
    (u : X ⟶ U) (a : U ⟶ V) (b : V ⟶ W) (j : U ⟶ Z) (q : Z ⟶ W)
    (t : F.obj W ⟶ Y) (t₀ : F.obj Z ⟶ T) (c : T ⟶ Y) (v : F.obj X ⟶ T)
    (hc : a ≫ b = j ≫ q) (ht : F.map q ≫ t = t₀ ≫ c)
    (hu : F.map u ≫ F.map j ≫ t₀ = v) :
    F.map (u ≫ a) ≫ (F.map b ≫ t) = v ≫ c := by
  calc
    _ = F.map u ≫ F.map (a ≫ b) ≫ t := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map u ≫ F.map j ≫ t₀ ≫ c := by
      rw [hc, F.map_comp, Category.assoc, ht]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ c) hu

private theorem homDiagramComparison_unit (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    (hp : ∀ m : ℕ,
      ((extension φ).mapHomologicalComplex (.up ℤ)).map
          (ringedKoszulProjection R r a m) ≫ (scalarTensorComparison φ).j.hom =
        e.hom.app m ≫ ringedKoszulProjection B r (imageSections φ a) m)
    (N : ringedSiteComplex B) (m : ℕᵒᵖ) :
    (restrictComplex φ).map ((ringedHomUnitEvaluationIso B N).inv ≫
      ((homComplexFunctor (R := B)).map
        (ringedKoszulProjection B r (imageSections φ a) m.unop).op).app N) ≫
      (homDiagramComparison φ r a e N).hom.app m =
    (ringedHomUnitEvaluationIso R ((restrictComplex φ).obj N)).inv ≫
      ((homComplexFunctor (R := R)).map
        (ringedKoszulProjection R r a m.unop).op).app ((restrictComplex φ).obj N) := by
  have hc :
      ((homComplexFunctor (R := B)).map
          (ringedKoszulProjection B r (imageSections φ a) m.unop).op).app N ≫
        ((homComplexFunctor (R := B)).map (e.hom.app m.unop).op).app N =
      ((homComplexFunctor (R := B)).map (scalarTensorComparison φ).j.hom.op).app N ≫
        ((homComplexFunctor (R := B)).map
          (((extension φ).mapHomologicalComplex (.up ℤ)).map
            (ringedKoszulProjection R r a m.unop)).op).app N := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      ← hp m.unop, op_comp, Functor.map_comp, NatTrans.comp_app]
  have ht := (SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta_natural
    (ringedSiteRingComplex R) ((ringedKoszulDiagram R r a).obj m.unop)
    N N (ringedKoszulProjection R r a m.unop) (𝟙 N)
  simp only [SheafOfModules.StrictScalarHom.homMap, Functor.map_id,
    Category.comp_id] at ht
  exact homUnitCompositionCore (restrictComplex φ)
    (ringedHomUnitEvaluationIso B N).inv
    (((homComplexFunctor (R := B)).map
      (ringedKoszulProjection B r (imageSections φ a) m.unop).op).app N)
    (((homComplexFunctor (R := B)).map (e.hom.app m.unop).op).app N)
    (((homComplexFunctor (R := B)).map (scalarTensorComparison φ).j.hom.op).app N)
    (((homComplexFunctor (R := B)).map
      (((extension φ).mapHomologicalComplex (.up ℤ)).map
        (ringedKoszulProjection R r a m.unop)).op).app N)
    ((SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta
      ((ringedKoszulDiagram R r a).obj m.unop) N).hom
    ((SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta
      (ringedSiteRingComplex R) N).hom
    (((homComplexFunctor (R := R)).map
      (ringedKoszulProjection R r a m.unop).op).app ((restrictComplex φ).obj N))
    (ringedHomUnitEvaluationIso R ((restrictComplex φ).obj N)).inv
    hc ht (homUnitScalar φ N)

/-- Coaugmentation of the scalar Koszul comparison.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Canonical evaluation carries the tensor coaugmentation to the inverse Hom-unit
evaluation followed by precomposition with the Koszul projection. This is the existing normalized
evaluation-unit identity.
Proof step 2: Check the scalar theta unit identity using its normalized local evaluation formula:
on sections the scalar-extension unit generator is exactly multiplication. Invert this identity
to obtain compatibility of inverse Hom-unit evaluations.
Proof step 3: Naturality of theta with the Koszul projection and the assumed projection
compatibility give the Hom diagram unit identity. Cancel the R Koszul evaluation isomorphism and
substitute steps 1 and 2 to get the tensor diagram coaugmentation identity.
(blueprint: lem-f5-koszul-scalar-hom-unit). -/
private theorem tensorDiagramComparison_unit (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    (hp : ∀ m : ℕ,
      ((extension φ).mapHomologicalComplex (.up ℤ)).map
          (ringedKoszulProjection R r a m) ≫ (scalarTensorComparison φ).j.hom =
        e.hom.app m ≫ ringedKoszulProjection B r (imageSections φ a) m)
    (N : ringedSiteComplex B) (m : ℕᵒᵖ) :
    (restrictComplex φ).map
        (ringedKoszulTensorUnitComponent B r (imageSections φ a) N m) ≫
        (tensorDiagramComparison φ r a e N).hom.app m =
      ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m := by
  apply (cancel_mono ((koszulEvaluation R r a ((restrictComplex φ).obj N)).hom.app m)).mp
  simp only [tensorDiagramComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc, ← Functor.map_comp, koszulEvaluation_unit,
    homDiagramComparison_unit φ r a e hp, koszulEvaluation_unit]

end CategoryTheory.FlatScalarKoszul
