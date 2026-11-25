/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.LargeSetSheafification
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Mathlib.Topology.Algebra.OpenSubgroup
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.LatticePullbackProof.ContinuousCoefficientPullbackIsoSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement

/-! # Finite free local models of continuous rational sheaves

Source: Bhatt--Scholze, Definitions 6.8.1, 6.8.6 and 6.8.10
(blueprint: lem-per-rational-continuous-finite-free-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
namespace AlgebraicGeometry.ProEtale
private def model (X : Scheme.{u}) (A : Type u) [TopologicalSpace A] [Field A]
    [IsTopologicalRing A] : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
  SheafOfModules.{u + 1} (latticeModuleRing X A) :=
  Scheme.adicLisseConstantModules X (ULift.{u + 1} A) ⋙
  Scheme.pbcExtend (continuousCoefficientConstantMap X A)
private def finiteModelIso (X : Scheme.{u}) (A : Type u) [TopologicalSpace A] [Field A]
    [IsTopologicalRing A] (P : ModuleCat.{u + 1} (ULift.{u + 1} A))
    [Module.Finite (ULift.{u + 1} A) P] :
  (model X A).obj P ≅ SheafOfModules.free (R := latticeModuleRing X A)
    (ULift.{u + 1} (Fin (Module.finrank (ULift.{u + 1} A) P))) := by
  let K := ULift.{u + 1} A
  let I := ULift.{u + 1} (Fin (Module.finrank K P))
  let b := (Module.finBasis K P).reindex Equiv.ulift.symm
  letI : Fintype I := inferInstance
  let e : P ≅ ModuleCat.of K (I → K) := b.equivFun.toModuleIso
  let F := model X A
  letI : Abelian (SheafOfModules.{u + 1} (latticeModuleRing X A)) := inferInstance
  letI : HasFiniteBiproducts (SheafOfModules.{u + 1} (latticeModuleRing X A)) :=
    CategoryTheory.Abelian.hasFiniteBiproducts
  have : (Scheme.adicLisseConstantModules X K).Additive :=
    Scheme.CompletedConstantReduction.constant_additive X K
  have : (Scheme.pbcExtend (continuousCoefficientConstantMap X A)).Additive := inferInstance
  have : F.Additive := by
    change (Scheme.adicLisseConstantModules X K ⋙
      Scheme.pbcExtend (continuousCoefficientConstantMap X A)).Additive
    infer_instance
  let z : F.obj (ModuleCat.of K K) ≅ SheafOfModules.unit (latticeModuleRing X A) :=
    Scheme.CompletedConstantReduction.constantChange_unit X (continuousCoefficientConstantMap X A)
  letI : HasBiproduct (fun _ : I ↦ ModuleCat.of K K) := HasBiproduct.of_hasProduct _
  letI : HasBiproduct (fun _ : I ↦ SheafOfModules.unit (latticeModuleRing X A)) :=
    HasBiproduct.of_hasProduct _
  let ep : (⨁ fun _ : I ↦ ModuleCat.of K K) ≅ ModuleCat.of K (I → K) :=
    IsLimit.conePointUniqueUpToIso (biproduct.isLimit _)
      (ModuleCat.HasLimit.productLimitCone.{u + 1, u + 1, u + 1}
        (fun _ : I ↦ ModuleCat.of K K)).isLimit
  exact F.mapIso e ≪≫ F.mapIso ep.symm ≪≫
    F.mapBiproduct (fun _ : I ↦ ModuleCat.of K K) ≪≫
    biproduct.mapIso (fun _ ↦ z) ≪≫ biproduct.isoCoproduct (fun _ : I ↦
      SheafOfModules.unit (latticeModuleRing X A))

private def freeModelIso (X : Scheme.{u}) (A : Type u) [TopologicalSpace A] [Field A]
    [IsTopologicalRing A] (I : Type (u + 1)) [Finite I] :
    (model X A).obj (ModuleCat.of (ULift.{u + 1} A) (I → ULift.{u + 1} A)) ≅
      SheafOfModules.free (R := latticeModuleRing X A) I := by
  letI := Fintype.ofFinite I
  let K := ULift.{u + 1} A
  let F := model X A
  letI : Abelian (SheafOfModules.{u + 1} (latticeModuleRing X A)) := inferInstance
  letI : HasFiniteBiproducts (SheafOfModules.{u + 1} (latticeModuleRing X A)) :=
    CategoryTheory.Abelian.hasFiniteBiproducts
  have : (Scheme.adicLisseConstantModules X K).Additive :=
    Scheme.CompletedConstantReduction.constant_additive X K
  have : F.Additive := by
    change (Scheme.adicLisseConstantModules X K ⋙
      Scheme.pbcExtend (continuousCoefficientConstantMap X A)).Additive
    infer_instance
  let z : F.obj (ModuleCat.of K K) ≅ SheafOfModules.unit (latticeModuleRing X A) :=
    Scheme.CompletedConstantReduction.constantChange_unit X (continuousCoefficientConstantMap X A)
  letI : HasBiproduct (fun _ : I ↦ ModuleCat.of K K) := HasBiproduct.of_hasProduct _
  letI : HasBiproduct (fun _ : I ↦ SheafOfModules.unit (latticeModuleRing X A)) :=
    HasBiproduct.of_hasProduct _
  let ep : (⨁ fun _ : I ↦ ModuleCat.of K K) ≅ ModuleCat.of K (I → K) :=
    IsLimit.conePointUniqueUpToIso (biproduct.isLimit _)
      (ModuleCat.HasLimit.productLimitCone.{u + 1, u + 1, u + 1}
       (fun _ : I ↦ ModuleCat.of K K)).isLimit
  exact F.mapIso ep.symm ≪≫
    F.mapBiproduct (fun _ : I ↦ ModuleCat.of K K) ≪≫
    biproduct.mapIso (fun _ ↦ z) ≪≫
    biproduct.isoCoproduct (fun _ : I ↦ SheafOfModules.unit (latticeModuleRing X A))

private theorem finiteLocalModels_iff (X : Scheme.{u}) (A : Type u)
    [TopologicalSpace A] [Field A] [IsTopologicalRing A]
    (M : SheafOfModules.{u + 1} (latticeModuleRing X A)) :
    (∃ (I : Type (u + 1)) (V : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i : I, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A),
        Module.FinitePresentation (ULift.{u + 1} A) P ∧
        Nonempty (M.over (V i) ≅ ((model X A).obj P).over (V i))) ↔
      M.IsFiniteLocallyFree := by
  classical
  let K := ULift.{u + 1} A
  constructor
  · rintro ⟨I, V, hV, h⟩
    let P (i : I) := (h i).choose
    have hP (i : I) : Module.FinitePresentation K (P i) := (h i).choose_spec.1
    let κ (i : I) := ULift.{u + 1} (Fin (Module.finrank K (P i)))
    refine SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free.{u + 1, u, u + 1} V hV κ ?_
    intro i
    have := hP i
    obtain ⟨e⟩ := (h i).choose_spec.2
    let O := SheafOfModules.overFunctor (latticeModuleRing X A) (V i)
    have : O.IsLeftAdjoint := by
      change (SheafOfModules.pushforward (𝟙 ((latticeModuleRing X A).over (V i)))).IsLeftAdjoint
      infer_instance
    exact ⟨e ≪≫ O.mapIso (finiteModelIso X A (P i)) ≪≫
      (SheafOfModules.mapFreeIso O (κ i) (Iso.refl _)).symm⟩
  · intro hM
    obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
    have := hq
    refine ⟨q.I, q.X, q.coversTop, fun i ↦ ?_⟩
    have := hf.isFiniteType i
    let κ := (q.generators i).I
    let P := ModuleCat.of K (κ → K)
    refine ⟨P, inferInstance, ⟨?_⟩⟩
    let O := SheafOfModules.overFunctor (latticeModuleRing X A) (q.X i)
    have : O.IsLeftAdjoint := by
      change (SheafOfModules.pushforward
        (𝟙 ((latticeModuleRing X A).over (q.X i)))).IsLeftAdjoint
      infer_instance
    exact (asIso (q.generators i).π).symm ≪≫
      SheafOfModules.mapFreeIso O κ (Iso.refl _) ≪≫
      O.mapIso (freeModelIso X A κ).symm

open Scheme
private theorem finiteFree_restrict_iff (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : R ≅ S)
    (M : pbcModules X S) :
    ((pbcRestrict c.hom).obj M).IsFiniteLocallyFree ↔ M.IsFiniteLocallyFree := by
  let e := (adicLisseForget X).mapIso c
  constructor
  · intro h
    have := h
    have q := finiteLocallyFree_restrict (ProEt.topology X) _ _ e.symm
      ((pbcRestrict c.hom).obj M)
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := q)
      ((WeilConjectures.restrictionRoundTrip e).app M)
  · intro h
    have := h
    exact finiteLocallyFree_restrict (ProEt.topology X) _ _ e M

private def extendIsoRestrict (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : R ≅ S) :
    pbcExtend c.hom ≅ pbcRestrict c.inv := by
  let e := (adicLisseForget X).mapIso c
  exact (pbcScalarAdjunction c.hom).leftAdjointUniq
    (WeilConjectures.restrictionEquivalence e.symm).toAdjunction

private def pullRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [Field T] [IsTopologicalRing T]
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (e : latticeCoefficientSheaf Y T ≅ R)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf Y T) ≅ latticeCoefficientSheaf X T)
    (hc : c.hom = continuousCoefficientInverseImageMap f T)
    (M : pbcModules Y R) :
    continuousModulePullback f T ((pbcRestrict e.hom).obj M) ≅
      (pbcRestrict (c.inv ≫ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map e.hom)).obj
        ((proEtaleModuleInverseImage f R).obj M) := by
  let N := (proEtaleModuleInverseImage f (latticeCoefficientSheaf Y T)).obj
    ((pbcRestrict e.hom).obj M)
  let a := AlgebraicGeometry.ProEtaleTensorComparison.scalarIdentification f e.hom M
  let q := eqToIso (Scheme.reductionChange_obj_eq X
    (continuousCoefficientInverseImageMap f T) N)
  let z : pbcExtend (continuousCoefficientInverseImageMap f T) ≅ pbcRestrict c.inv :=
    eqToIso (congrArg (fun k ↦ pbcExtend k) hc.symm) ≪≫ extendIsoRestrict X c
  exact q.symm ≪≫ (pbcExtend (continuousCoefficientInverseImageMap f T)).mapIso a ≪≫
    z.app _ ≪≫
      (pbcRestrictComp c.inv ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map e.hom)
        (c.inv ≫ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map e.hom) rfl).app _

private theorem coefficientTotallyDisconnected (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    TotallyDisconnectedSpace (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) := by
  let T := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let : IsUltrametricDist T := by
    constructor
    intro x y z
    dsimp only [T] at x y z ⊢
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub]
    change spectralNorm ℚ_[l] E (x.ofAbs - z.ofAbs) ≤
      max (spectralNorm ℚ_[l] E (x.ofAbs - y.ofAbs))
        (spectralNorm ℚ_[l] E (y.ofAbs - z.ofAbs))
    simpa only [sub_add_sub_cancel] using
      (isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E))
        (x.ofAbs - y.ofAbs) (y.ofAbs - z.ofAbs)
  infer_instance

private theorem criterionTest (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.ContinuousRational.Base.{u} l)
    (e : latticeCoefficientSheaf X.scheme
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
        rationalCoefficientSheaf l X.scheme E)
    (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) :
    Scheme.ContinuousRational.IsConstructible l E X.scheme e M ↔
      ∃ s : Scheme.FiniteLocallyClosedStratification X.scheme, ∀ i : Fin s.n,
        ((proEtaleModuleInverseImage (s.immersion i)
          (rationalCoefficientSheaf l X.scheme E)).obj M).IsFiniteLocallyFree := by
  let T := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  have : TotallyDisconnectedSpace T := coefficientTotallyDisconnected l E
  have transport (Y : Scheme.{u}) (f : Y ⟶ X.scheme) :
      (∃ (I : Type (u + 1)) (V : I → Y.ProEt),
        (ProEt.topology Y).CoversTop V ∧
        ∀ i : I, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} T),
          Module.FinitePresentation (ULift.{u + 1} T) P ∧
          Nonempty ((continuousModulePullback f T ((pbcRestrict e.hom).obj M)).over (V i) ≅
            (continuousCoefficientModule Y T P).over (V i))) ↔
        ((proEtaleModuleInverseImage f
          (rationalCoefficientSheaf l X.scheme E)).obj M).IsFiniteLocallyFree := by
    let := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso f T
    let c := asIso (continuousCoefficientInverseImageMap f T)
    let d := c.symm ≪≫ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso e
    let N := (proEtaleModuleInverseImage f (rationalCoefficientSheaf l X.scheme E)).obj M
    let b := pullRestrictIso f T e c rfl M
    have hlocal := finiteLocalModels_iff Y T
      (continuousModulePullback f T ((pbcRestrict e.hom).obj M))
    have hfree :
        (continuousModulePullback f T ((pbcRestrict e.hom).obj M)).IsFiniteLocallyFree ↔
        ((pbcRestrict d.hom).obj N).IsFiniteLocallyFree := by
      constructor
      · intro h
        exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := h) b
      · intro h
        exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := h) b.symm
    have hp := (finiteFree_restrict_iff Y d N)
    have hm (P : ModuleCat.{u + 1} (ULift.{u + 1} T)) :
        continuousCoefficientModule Y T P = (model Y T).obj P :=
      (Scheme.reductionChange_obj_eq Y (continuousCoefficientConstantMap Y T) _).symm
    simp_rw [hm]
    exact hlocal.trans (hfree.trans hp)
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.toFiniteLocallyClosed, fun i ↦ (transport (s.domain i) (s.immersion i)).mp (hs i)⟩
  · rintro ⟨s, hs⟩
    let t := s.withConstructibleStrata (fun i ↦
      (s.isLocallyClosed_stratum i).isConstructible_of_noetherianSpace)
    exact ⟨t, fun i ↦ (transport (s.domain i) (s.immersion i)).mpr (hs i)⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- Over a coefficient field the finitely presented continuous local models are exactly
finite locally free models. The normalized coefficient encoding preserves this condition.
Source: Bhatt--Scholze, Definitions 6.8.1, 6.8.6 and 6.8.10
(blueprint: lem-per-rational-continuous-finite-free-criterion).

Proof: the spectral absolute value is nonarchimedean, so its WithAbs field is
ultrametric and totally disconnected. Its continuous inverse-image coefficient map is
therefore an isomorphism for every scheme morphism. The scalar-identification comparison
and uniqueness of left adjoints identify continuous pullback after coefficient encoding
with restriction of the site inverse image along a ring isomorphism. Restriction along
an isomorphism preserves and reflects finite local freeness. A finitely presented module
over the field is finite dimensional; a finite basis identifies its additive continuous
constant model with a finite coproduct of the coefficient unit. Conversely a finite free
sheaf is the continuous constant model of a finite product field module. The over functor
preserves these free-unit identifications on every covering object. A finite locally
closed stratification of a noetherian space has constructible strata; equip the same
stratification with these certificates. Zero rank and the empty stratification are
allowed. This argument works for every coefficient ring isomorphism e, so its pointwise
normalization hypothesis is not needed. -/
theorem rationalContinuousFiniteFreeCriterion (X : Base.{u} l)
    (e : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X.scheme
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
        rationalCoefficientSheaf l X.scheme E)
    (he : ∀ (U : X.scheme.ProEtᵒᵖ)
      (f : C(U.unop.left, WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
      (x : U.unop.left),
      rationalCoefficientValue l E X.scheme U (e.hom.hom.app U (ULift.up f)) x =
        WithAbs.ofAbs (f x)) :
    ∀ F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E),
      IsConstructible l E X.scheme e F ↔
        ∃ s : FiniteLocallyClosedStratification X.scheme, ∀ i : Fin s.n,
          ((proEtaleModuleInverseImage (s.immersion i)
            (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree := by
  have _ := he
  exact AlgebraicGeometry.ProEtale.criterionTest l E X e

end AlgebraicGeometry.Scheme.ContinuousRational
