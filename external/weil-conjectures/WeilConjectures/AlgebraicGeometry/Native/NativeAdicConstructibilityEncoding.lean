/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# Constructibility under the native adic encoding

## References

* Bhatt--Scholze, Definitions 6.8.3 and 6.8.8
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable {l : ℕ} [Fact l.Prime]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_map {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) : Mod.IsFree S (F.obj M) := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨F.mapIso i ≪≫ F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e)⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  apply encoding_free_map (Mod.comap φ) _ h
  simpa using Mod.regularIsoOfIsIso (inv φ)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree S M := by
  exact encoding_free_of_iso (encoding_free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_fp_of_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFree R M) : Mod.IsFinitelyPresented R M := by
  obtain ⟨n, ⟨i⟩⟩ := hM
  exact ⟨n, n, 0, ⟨i ≪≫ cokernelZeroIsoTarget.symm⟩⟩

private noncomputable def encoding_regular (T : Scheme.{u}) :
    (NativeEncoding.encoding l T).obj (AdicSheaf.unit l T) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T) := by
  let e : (AdicSheaf.forgetAb l T).obj (AdicSheaf.unit l T) ≅
      Mod.regular ((weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T)) :=
    Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  refine (Mod.comap (NativeEncoding.coefficientIso l T).hom).mapIso e ≪≫ ?_
  simpa only [IsIso.inv_inv] using
    Mod.regularIsoOfIsIso (inv (NativeEncoding.coefficientIso l T).hom)

private noncomputable def encoding_free (T : Scheme.{u}) (r : ℕ) :
    (NativeEncoding.encoding l T).obj (Mod.finiteFree (adicConstantSheaf l T) r) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) T) r :=
  (NativeEncoding.encoding l T).mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ encoding_regular T)

private theorem encoding_lisse_iff {T : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T] (M : AdicSheaf l T) :
    IsAdicLisseSheaf M ↔
      IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj l) T)
        ((NativeEncoding.encoding l T).obj M) := by
  classical
  constructor
  · intro hM
    obtain ⟨R, hR, h⟩ := hM
    obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage T :=
      { I₀ := ι, X := V, f := f, mem₀ := hR }
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage (@WeaklyEtale)))
    let C := D.restrictIndexOfSmall.{u}
    refine ⟨C, fun i ↦ ?_⟩
    let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} D i
    obtain ⟨r, ⟨e⟩⟩ := h (f j) (.mk j)
    have hfree : Mod.IsFree _
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (C.f i)).obj
          ((NativeEncoding.encoding l T).obj M)) :=
      ⟨r, ⟨((NativeEncoding.pullComparison l (C.f i)).app M).symm ≪≫
        (NativeEncoding.encoding l (C.X i)).mapIso e ≪≫ encoding_free (C.X i) r⟩⟩
    let φ := condensedPullbackHom (Profinite.padicAlgClRingObj l) (C.f i)
    have hraw : Mod.IsFree _ ((Mod.comap (inv φ)).obj
        (((upperStar Ab.{u + 1} (C.f i)).mapMod _).obj
          ((NativeEncoding.encoding l T).obj M))) :=
      encoding_free_of_iso hfree ((Mod.extendScalarsIsoComapInv φ).app _)
    exact encoding_fp_of_free (encoding_free_of_comap (inv φ) hraw)
  · intro hM
    obtain ⟨C, hC⟩ := condensedQbar_lfp_locally_free l T _ hM
    refine ⟨C.presieve₀, C.mem₀, ?_⟩
    rintro _ _ ⟨i⟩
    obtain ⟨r, ⟨e⟩⟩ := hC i
    exact ⟨r, ⟨(NativeEncoding.encoding l (C.X i)).preimageIso
      (((NativeEncoding.pullComparison l (C.f i)).app M) ≪≫ e ≪≫
        (encoding_free (C.X i) r).symm)⟩⟩

/-- The normalized native encoding preserves and detects constructibility on a Noetherian
scheme. -/
theorem encoding_constructible_iff {T : Scheme.{u}} [IsNoetherian T]
    (M : AdicSheaf l T) :
    IsAdicConstructibleSheaf M ↔
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj l) T)
        ((NativeEncoding.encoding l T).obj M) := by
  classical
  have hrestriction (Z : Scheme.{u}) (i : Z ⟶ T) [IsImmersion i] :
      IsAdicLisseSheaf ((adicUpperStar l i).obj M) ↔
        IsLocallyFinitelyPresented
          ((upperStar Ab.{u + 1} i).obj
            (condensedRingObj (Profinite.padicAlgClRingObj l) T))
          (((upperStar Ab.{u + 1} i).mapMod _).obj
            ((NativeEncoding.encoding l T).obj M)) := by
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isEmbedding.noetherianSpace
    rw [encoding_lisse_iff]
    let φ := condensedPullbackHom (Profinite.padicAlgClRingObj l) i
    let N := (((upperStar Ab.{u + 1} i).mapMod _).obj
      ((NativeEncoding.encoding l T).obj M))
    have e : (NativeEncoding.encoding l Z).obj ((adicUpperStar l i).obj M) ≅
        (Mod.comap (inv φ)).obj N :=
      (NativeEncoding.pullComparison l i).app M ≪≫
        (Mod.extendScalarsIsoComapInv φ).app N
    exact ⟨fun h ↦ localFinitePresentation_of_comap (inv φ)
        (localFinitePresentation_of_iso e h),
      fun h ↦ localFinitePresentation_of_iso e.symm
        (localFinitePresentation_comap (inv φ) h)⟩
  constructor
  · intro hM
    obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hM.isAdicStratifiedLisseSheaf
    let := hι
    let := Fintype.ofFinite ι
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    let S : Scheme.Stratification T :=
      { n := Fintype.card ι
        stratum := fun r ↦ Set.range (i (e r))
        isLocallyClosed_stratum := fun r ↦ by
          have := hi (e r)
          exact (i (e r)).isLocallyClosed_range
        isConstructible_stratum := fun r ↦ hc (e r)
        iUnion_stratum_eq_univ := by
          apply Set.eq_univ_of_forall
          intro x
          obtain ⟨k, hk, -⟩ := hcover x
          refine Set.mem_iUnion.mpr ⟨e.symm k, ?_⟩
          dsimp only
          rw [e.apply_symm_apply]
          exact hk
        pairwise_disjoint_stratum := by
          intro r s hrs
          apply Set.disjoint_left.mpr
          intro x hxr hxs
          obtain ⟨k, -, hk⟩ := hcover x
          exact hrs (e.injective ((hk _ hxr).trans (hk _ hxs).symm))
        domain := fun r ↦ Z (e r)
        immersion := fun r ↦ i (e r)
        isImmersion := fun r ↦ hi (e r)
        range_immersion := fun _ ↦ rfl }
    exact ⟨S, fun r ↦ (hrestriction _ _).mp (h (e r))⟩
  · rintro ⟨S, hS⟩
    apply IsAdicStratifiedLisseSheaf.isAdicConstructibleSheaf
    refine ⟨Fin S.n, inferInstance, S.domain, S.immersion, S.isImmersion,
      fun i ↦ S.range_immersion i ▸ S.isConstructible_stratum i, ?_,
      fun i ↦ (hrestriction _ _).mpr (hS i)⟩
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    refine ⟨i, ?_, fun j hj ↦ ?_⟩
    · change x ∈ Set.range (S.immersion i)
      rwa [S.range_immersion i]
    · change x ∈ Set.range (S.immersion j) at hj
      by_contra hji
      exact Set.disjoint_left.mp (S.pairwise_disjoint_stratum hji) (by
        rwa [S.range_immersion j] at hj) hi

end AlgebraicGeometry.ProEtale
