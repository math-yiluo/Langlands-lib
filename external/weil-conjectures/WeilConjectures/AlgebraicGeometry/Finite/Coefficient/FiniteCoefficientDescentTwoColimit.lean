/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentLisse
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Finite coefficient descent and the rational coefficient two-colimit

Source: Weil blueprint main-20261015, chap-Construction-of-f,
sk-thm-sfb-qlbar-two-colimit/_section.md, assertions (1)--(4)
(blueprint: lemma-descent-finite-coefficient-field).

The shifted Hom-colimit isomorphism is expressed by its representative and eventual
equality conditions. We write the shifted target as T(D[r]); exact scalar extension
canonically identifies this with (TD)[r]. Every transition and evaluation is the
specified scalar-extension map, conjugated by canonical tensor transitivity.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.CommShift.ofIso Functor.leftDerivedFunctor Functor.mapDerivedCategory

/-- The canonical derived scalar comparison for three finite coefficient fields.
Source: blueprint lemma-descent-finite-coefficient-field, definition of C_F and proof (4),
tensor transitivity (blueprint: lemma-descent-finite-coefficient-field).
This is the existing exact-functor comparison applied to the ordinary tensor comparison.
-/
def finiteDescentDerivedComp (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H) :
    derivedExtendScalarsSubfield X ℓ (h.trans a) ≅
      derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsSubfield X ℓ a :=
  Functor.leftDerivedFunctorNatIso _ (lisseFiniteExtensionCompIso X ℓ h a) ≪≫
    Functor.leftDerivedFunctorCompIso _ _

/-- Evaluate a finite-field derived Hom representative in the algebraic closure.
Source: blueprint lemma-descent-finite-coefficient-field, displayed isomorphism (2)
(blueprint: lemma-descent-finite-coefficient-field). -/
def finiteDescentDerivedHomToAlgCl (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    {C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj D) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ E).obj D :=
  (derivedExtendScalarsCompIso X ℓ h).inv.app C ≫
    (derivedExtendScalarsToPadicAlgCl X ℓ F).map f ≫
      (derivedExtendScalarsCompIso X ℓ h).hom.app D

/-- The transition between finite-field Hom representatives, using tensor transitivity.
Source: blueprint lemma-descent-finite-coefficient-field, displayed colimit (2) and proof (4)
(blueprint: lemma-descent-finite-coefficient-field). -/
def finiteDescentDerivedHomTransition (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H)
    {C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj D) :
    (derivedExtendScalarsSubfield X ℓ (h.trans a)).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ (h.trans a)).obj D :=
  (finiteDescentDerivedComp X ℓ h a).hom.app C ≫
    (derivedExtendScalarsSubfield X ℓ a).map f ≫
      (finiteDescentDerivedComp X ℓ h a).inv.app D

open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_hasConstantModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ Y M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hU i
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesFiniteBiproducts F := inferInstance
  let en : F.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree (condensedRingObj Λ (U.X i)) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  refine ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

open MonoidalCategory MonObj in
private lemma constantModel_eq_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      IsConstantModelConstructible Λ X M ↔
        IsConstructibleModuleObject (condensedRingObj Λ X) M := by
    rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := (hS a).isLocallyFinitelyPresented _
      exact lfp_of_comap (inv φ)
        (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      have : TopologicalSpace.NoetherianSpace (S.domain a) :=
        (S.immersion a).isEmbedding.isInducing.noetherianSpace
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
        ((Mod.extendScalarsIsoComapInv φ).app _).symm
      obtain ⟨U, hU⟩ := hLF _ _ h
      apply free_hasConstantModel Λ _
      refine ⟨U, fun i ↦ ?_⟩
      let ψ := condensedPullbackHom Λ (U.f i)
      exact free_of_iso (free_comap (inv ψ) (hU i))
        ((Mod.extendScalarsIsoComapInv ψ).app _).symm
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ hmod _

private lemma scalarEq_refl (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] (f : R ⟶ S) [IsMonHom f] :
    Mod.extendScalarsIsoOfEq (rfl : f = f) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((Mod.extendRestrictAdjunction f).homEquiv _ _).injective
  simp [Mod.extendScalarsIsoOfEq, Adjunction.homEquiv_unit]
  rfl

private lemma scalarEq_symm (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R]
    {f g : R ⟶ S} [IsMonHom f] [IsMonHom g] (h : f = g) :
    Mod.extendScalarsIsoOfEq h.symm = (Mod.extendScalarsIsoOfEq h).symm := by
  subst g
  simp only [scalarEq_refl]
  rfl

private lemma finiteDescentDerivedComp_eq (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H) :
    finiteDescentDerivedComp X ℓ h a = (condensedCoefficientCompIso X ℓ h a).symm := by
  have he : lisseFiniteExtensionCompIso X ℓ h a =
      ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
          (padicSubfieldRingObjMap X ℓ a)).symm ≪≫
        Mod.extendScalarsIsoOfEq (condensedCoefficientMap_comp X ℓ h a)).symm := by
    simp only [lisseFiniteExtensionCompIso, Iso.trans_symm, Iso.symm_symm_eq]
    rw [← scalarEq_symm]
  unfold finiteDescentDerivedComp condensedCoefficientCompIso
  rw [he]
  apply Iso.ext
  simp only [Functor.leftDerivedFunctorNatIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private lemma finiteDescentDerivedHomToAlgCl_zero
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj D) :
    coefficientDescentHomToAlgCl X ℓ h C D 0
        (f ≫ (shiftFunctorZero _ ℤ).inv.app _) ≫ (shiftFunctorZero _ ℤ).hom.app _ =
      finiteDescentDerivedHomToAlgCl X ℓ h f := by
  simp [coefficientDescentHomToAlgCl, coefficientDescentDerivedHomMap,
    Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
    finiteDescentDerivedHomToAlgCl, Functor.map_comp, Category.assoc]

private lemma finiteDescentDerivedHomTransition_zero
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj D) :
    coefficientDescentHomTransition X ℓ h a C D 0
        (f ≫ (shiftFunctorZero _ ℤ).inv.app _) ≫ (shiftFunctorZero _ ℤ).hom.app _ =
      finiteDescentDerivedHomTransition X ℓ h a f := by
  simp [coefficientDescentHomTransition, coefficientDescentDerivedHomMap,
    Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
    finiteDescentDerivedHomTransition, finiteDescentDerivedComp_eq,
    Functor.map_comp, Category.assoc]

attribute [local irreducible] finiteCoefficientDerivedHomEquiv finiteCoefficientDerivedAlgClHomEquiv
  finiteDescentDerivedHomToAlgCl finiteDescentDerivedHomTransition
  coefficientDescentHomToAlgCl coefficientDescentHomTransition

/-- The equality part of clause (4) of `finiteCoefficientDescentTwoColimit` on its own: for a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a noetherian qcqs scheme `X`, the constant-model
bounded constructible complexes with `E`-coefficients are the bounded constructible ones (the
clause also carries the compatibilities under extension of scalars, which stay in the bundle).
Every user of the descent bundle needs only this equality. -/
theorem constantModelBoundedConstructible_eq_boundedConstructible_subfield
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
      boundedConstructible (padicSubfieldRingObj X ℓ E) :=
  constantModel_eq_of_localFree _ (finite_lf ℓ E) X

/-- The equality part of clause (4) of `finiteCoefficientDescentTwoColimit` on its own: for a
noetherian qcqs scheme `X`, the constant-model bounded constructible complexes with
`ℚ̄_ℓ`-coefficients are the bounded constructible ones. -/
theorem constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
      boundedConstructible (padicAlgClRingObj X ℓ) :=
  constantModel_eq_of_localFree _ (algcl_lf ℓ) X

/-- `constantModelBoundedConstructible_eq_boundedConstructible_subfield` for a scheme of finite
type over a field, the form the six-functor files use. -/
theorem constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
      boundedConstructible (padicSubfieldRingObj X ℓ E) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact constantModelBoundedConstructible_eq_boundedConstructible_subfield ℓ E X

/-- `constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl` for a scheme of finite
type over a field, the form the six-functor files use. -/
theorem constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
      boundedConstructible (padicAlgClRingObj X ℓ) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl ℓ X

/-- Ordinary derived Hom descent, with the degree-zero comparison normalized once. -/
private lemma finiteDescentDerivedHom_bijective
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact p.Prime] [Fact ℓ.Prime]
    (hpℓ : p ≠ ℓ) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) :
    (∀ ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        (derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj D.obj),
        finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        (derivedExtendScalarsSubfield X ℓ h).obj D.obj)
      (g : (derivedExtendScalarsSubfield X ℓ a).obj C.obj ⟶
        (derivedExtendScalarsSubfield X ℓ a).obj D.obj),
      finiteDescentDerivedHomToAlgCl X ℓ h f = finiteDescentDerivedHomToAlgCl X ℓ a g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
        finiteDescentDerivedHomTransition X ℓ h b f =
          finiteDescentDerivedHomTransition X ℓ a c g) := by
  have hh := (coefficient_finite_descent_hom X ℓ (k := k) p hpℓ E C D 0).2.2.2.2.2
  have hs := hh.1
  have hi := hh.2
  constructor
  · intro ψ
    obtain ⟨F, h, f, hf⟩ := hs
      (ψ ≫ (shiftFunctorZero _ ℤ).inv.app
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj))
    refine ⟨F, h, f ≫ (shiftFunctorZero _ ℤ).hom.app
      ((derivedExtendScalarsSubfield X ℓ h).obj D.obj), ?_⟩
    have hz := finiteDescentDerivedHomToAlgCl_zero X ℓ h C.obj D.obj
      (f ≫ (shiftFunctorZero _ ℤ).hom.app
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj))
    have hz' : coefficientDescentHomToAlgCl X ℓ h C.obj D.obj 0 f ≫
        (shiftFunctorZero _ ℤ).hom.app
          ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj) =
        finiteDescentDerivedHomToAlgCl X ℓ h
          (f ≫ (shiftFunctorZero _ ℤ).hom.app
            ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)) := by
      simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using hz
    exact hz'.symm.trans
      ((congrArg (fun q ↦ q ≫ (shiftFunctorZero _ ℤ).hom.app
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)) hf).trans (by
        simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]))
  · intro F G h a f g heq
    have heq' : coefficientDescentHomToAlgCl X ℓ h C.obj D.obj 0
        (f ≫ (shiftFunctorZero _ ℤ).inv.app
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)) =
      coefficientDescentHomToAlgCl X ℓ a C.obj D.obj 0
        (g ≫ (shiftFunctorZero _ ℤ).inv.app
          ((derivedExtendScalarsSubfield X ℓ a).obj D.obj)) := by
      apply (cancel_mono ((shiftFunctorZero _ ℤ).hom.app
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj))).mp
      simpa only [finiteDescentDerivedHomToAlgCl_zero] using heq
    obtain ⟨H, b, c, he⟩ := hi F G h a
      (f ≫ (shiftFunctorZero _ ℤ).inv.app
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj))
      (g ≫ (shiftFunctorZero _ ℤ).inv.app
        ((derivedExtendScalarsSubfield X ℓ a).obj D.obj)) heq'
    refine ⟨H, b, c, ?_⟩
    have he' := congrArg (fun q ↦ q ≫ (shiftFunctorZero _ ℤ).hom.app
      ((derivedExtendScalarsSubfield X ℓ (h.trans b)).obj D.obj)) he
    simpa only [finiteDescentDerivedHomTransition_zero] using he'

/-- All four finite coefficient descent assertions, including the rational identification
and the ordinary-category filtered two-colimit.
Source: blueprint main-20261015, lemma-descent-finite-coefficient-field, assertions (1)--(4)
(blueprint: lemma-descent-finite-coefficient-field).

Proof: finite type and quasi-compactness make X Noetherian. On each Noetherian
stratum, finite constant models are locally finitely presented, and the finite-field
and algebraic-closure local-triviality theorems give the converse. Pullback preserves
finite free modules, so both constructibility predicates agree, also on cohomology.
Apply the existing lisse and object-descent theorems for assertions (1) and (3).
For (2), apply the Hom-descent theorem to C and D[r] at degree zero. The canonical
zero-shift isomorphism converts representatives and eventual equalities to the
maps in this statement. Tensor transitivity agrees with the specified comparison,
as follows by compatibility of scalar-map equality and derived isomorphism inversion.
For (4), the rational case of localizingClosure_ctf_equals_bc supplies finite Tor
amplitude, and constructibleCocone_isFilteredTwoColimit supplies the two-colimit of
the same canonical cocone. No definition or conclusion is changed.
-/
theorem finiteCoefficientDescentTwoColimit
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact ℓ.Prime]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L →
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (L_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L_E ∧
          Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj L_E ≅ L)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (C D : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X) (r : ℤ),
      (∀ ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj (D.obj⟦r⟧),
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
            (derivedExtendScalarsSubfield X ℓ h).obj (D.obj⟦r⟧)),
          finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj (D.obj⟦r⟧))
        (g : (derivedExtendScalarsSubfield X ℓ a).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ a).obj (D.obj⟦r⟧)),
        finiteDescentDerivedHomToAlgCl X ℓ h f = finiteDescentDerivedHomToAlgCl X ℓ a g →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
          finiteDescentDerivedHomTransition X ℓ h b f =
            finiteDescentDerivedHomTransition X ℓ a c g)) ∧
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    ((∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
          boundedConstructible (padicSubfieldRingObj X ℓ E) ∧
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
          DerivedCategory.finiteTorAmplitude _) =
            constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X) ∧
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
        boundedConstructible (padicAlgClRingObj X ℓ) ∧
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
        DerivedCategory.finiteTorAmplitude _) =
          constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ∧
      (constructibleCocone X ℓ).IsFilteredTwoColimit) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  let : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp)⟩
  have hE : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
        boundedConstructible (padicSubfieldRingObj X ℓ E) := by
    intro E
    exact constantModel_eq_of_localFree (Profinite.continuousMapRingObj E) (finite_lf ℓ E) X
  have hΩ : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
      boundedConstructible (padicAlgClRingObj X ℓ) := by
    exact constantModel_eq_of_localFree (Profinite.padicAlgClRingObj ℓ) (algcl_lf ℓ) X
  refine ⟨(coefficient_finite_descent_lisse X ℓ).1, ?_,
    (coefficient_finite_descent_objects k p ℓ hp hpℓ X).1, ?_⟩
  · intro E C D r
    let : (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated :=
      finiteBoundedTriangulated X ℓ E
    let C' : BoundedConstructible (padicSubfieldRingObj X ℓ E) :=
      ⟨C.obj, (congrFun (hE E) C.obj).mp C.property⟩
    let D' : BoundedConstructible (padicSubfieldRingObj X ℓ E) :=
      ⟨D.obj⟦r⟧, (boundedConstructible _).le_shift r D.obj
        ((congrFun (hE E) D.obj).mp D.property)⟩
    exact finiteDescentDerivedHom_bijective k p ℓ hpℓ X E C' D'
  · refine ⟨?_, ?_, constructibleCocone_isFilteredTwoColimit X ℓ⟩
    · intro E
      refine ⟨hE E, ?_⟩
      exact (localizingClosure_ctf_equals_bc ℓ X _
        (Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩)))).1.2.2.1
    · refine ⟨hΩ, ?_⟩
      exact (localizingClosure_ctf_equals_bc ℓ X _
        (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1

end AlgebraicGeometry.ProEtale
