/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
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
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
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
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-! # Shared proof API for finite coefficient descent

The private factorization, exact derived composition, and bounded constructibility
helpers formerly lived in the two-colimit and flat-coefficient proofs. They are kept
here so their earlier support-induction dependencies can reuse them without a cycle.
This module introduces no new mathematical obligation.
-/

@[expose] public section

universe u wC wD wE vC vD vE uC uD uE
open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

section HomFactorization
set_option linter.unusedSectionVars false
universe v w uI vI
open CategoryTheory.Pretriangulated Preadditive
namespace CategoryTheory
variable {D : Type w} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {I : Type uI} [Category.{vI} I] [IsFiltered I] {N : I ⥤ D} (c : Cocone N)

private def factors (K : D) : Prop :=
  ∀ f : K ⟶ c.pt, ∃ (i : I) (g : K ⟶ N.obj i), f = g ≫ c.ι.app i
private lemma factors_iso {K L : D} (e : K ≅ L) (h : factors c K) : factors c L := by
  intro f
  obtain ⟨i, g, hg⟩ := h (e.hom ≫ f)
  refine ⟨i, e.inv ≫ g, ?_⟩
  rw [Category.assoc, ← hg]
  simp
private def shiftFactors : ObjectProperty D :=
  fun K ↦ ∀ n : ℤ, factors c (K⟦n⟧)

private lemma shiftFactors_of_hom_colimit
    {A : Type*} [Category A] {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (S : D)
    (h : ∀ n : ℤ, IsIso (colimit.desc _
      ((Q ⋙ shiftFunctor D n ⋙ preadditiveCoyoneda.obj (Opposite.op S)).mapCocone
        (colimit.cocone N)))) :
    shiftFactors (Q.mapCocone (colimit.cocone N)) S := by
  intro n f
  let F := Q ⋙ shiftFunctor D (-n) ⋙ preadditiveCoyoneda.obj (Opposite.op S)
  let t := F.mapCocone (colimit.cocone N)
  let p := colimit.desc (N ⋙ F) t
  have : IsIso p := h (-n)
  let adj := (shiftEquiv D n).toAdjunction
  let ff := adj.homEquiv S _ f
  let z := (inv p) ff
  obtain ⟨i, g, hg⟩ := Concrete.colimit_exists_rep (N ⋙ F) z
  have hfg : p ((colimit.ι (N ⋙ F) i) g) = ff := by
    rw [hg]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id p) ff
  have he : g ≫ (Q.map (colimit.ι N i))⟦-n⟧' = ff := by
    change (colimit.ι (N ⋙ F) i ≫ p) g = ff at hfg
    rw [colimit.ι_desc] at hfg
    exact hfg
  refine ⟨i, (adj.homEquiv S _).symm g, ?_⟩
  apply (adj.homEquiv S _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact he.symm
private lemma factors_of_colimit_cocone
    {A : Type*} [Category A] {J : Type*} [Category J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (c : Cocone N) (hc : IsColimit c) (K : D)
    (h : factors (Q.mapCocone (colimit.cocone N)) K) : factors (Q.mapCocone c) K := by
  let e := (colimit.isColimit N).coconePointUniqueUpToIso hc
  have he (i : J) : colimit.ι N i ≫ e.hom = c.ι.app i :=
    (colimit.isColimit N).comp_coconePointUniqueUpToIso_hom hc i
  intro f
  obtain ⟨i, g, hg⟩ := h (f ≫ Q.map e.inv)
  change f ≫ Q.map e.inv = g ≫ Q.map (colimit.ι N i) at hg
  refine ⟨i, g, ?_⟩
  calc
    f = (f ≫ Q.map e.inv) ≫ Q.map e.hom := by simp
    _ = (g ≫ Q.map (colimit.ι N i)) ≫ Q.map e.hom := by rw [hg]
    _ = g ≫ Q.map (c.ι.app i) := by rw [Category.assoc, ← Q.map_comp, he]
end CategoryTheory
end HomFactorization
namespace CategoryTheory.Functor
section DerivedCompositionAPI
variable {C : Type uC} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]
  {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
private noncomputable abbrev derivedComp (e : F ⋙ G ≅ FG) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ FG.mapDerivedCategory :=
  (mapDerivedCategoryCompIso F G) ≪≫ mapDerivedCategoryNatIso e

end DerivedCompositionAPI
section TransportAPI
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {F F' : C ⥤ D} {G G' : D ⥤ E} {FG FG' : C ⥤ E}
private noncomputable abbrev transportComp (a : F ≅ F') (b : G ≅ G') (c : FG ≅ FG')
    (e : F' ⋙ G' ≅ FG') : F ⋙ G ≅ FG :=
  isoWhiskerLeft F b ≪≫ isoWhiskerRight a G' ≪≫ e ≪≫ c.symm

end TransportAPI
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftTransport
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

private lemma leftComp_transport (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    (F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e =
      transportComp F.leftDerivedFunctorIsoMapDerivedCategory
        G.leftDerivedFunctorIsoMapDerivedCategory FG.leftDerivedFunctorIsoMapDerivedCategory
        (derivedComp e) := by
  simp [leftDerivedFunctorCompIso, leftDerivedFunctorNatIso, transportComp, derivedComp,
    Iso.trans_assoc, ← isoWhiskerLeft_symm, ← isoWhiskerRight_symm]

private lemma leftComp_shift (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift ((F.leftDerivedFunctorCompIso G).symm ≪≫
      (F ⋙ G).leftDerivedFunctorNatIso e).hom ℤ := by
  let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift G.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift G.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift FG.leftDerivedFunctorIsoMapDerivedCategory.inv ℤ :=
    CommShift.ofIso_compatibility FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  rw [leftComp_transport]
  dsimp only [transportComp, derivedComp, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance
end LeftTransport
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
  (ℓ : ℕ) [Fact ℓ.Prime]

private lemma bounded_tri_of_serre {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hker : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧ IsConstructibleModuleObject R (cokernel f))
    (hext : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated :=
  isTriangulated_boundedConstructible_of_serre R hker hext
-- Build the specific condensed-field triangulated structures from their Serre closure
-- statements; no arbitrary-coefficient closure assertion is used.
/-- Bounded constructible complexes over a finite coefficient field form a triangulated
subcategory.

Source: `Colimit/TwoColimit.lean`, the private `finiteBoundedTriangulated` helper.
Proof: finite-field constructible modules are closed under kernels, cokernels, and
extensions by `isConstructibleModuleObject_serre_padicSubfield`. Transport these
closures across isomorphisms and apply the existing conditional bounded-constructible
triangulated instance. This extracts the existing proof without adding an obligation.
(blueprint: lem-weil-pbc-condensed-finite-model-proof-api)
-/
lemma finiteBoundedTriangulated (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated := by
  obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicSubfield X ℓ E
  exact bounded_tri_of_serre _ hk he
omit [TopologicalSpace.NoetherianSpace X] in
private lemma single_bounded_constructible
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : IsConstructibleModuleObject R M) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  have hzero (n : ℤ) (hn : n ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj K) := by
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact constructible_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · exact constructible_of_isZero R _ (hzero n hn)

end AlgebraicGeometry.ProEtale
