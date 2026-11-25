/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
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
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
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
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.AlgebraicGeometry.CondensedLocalCoefficientAdjoints
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree

/-! # Finite-stage lifting of lisse coefficient morphisms
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A lisse coefficient module is locally free over its coefficient ring: the free
trivializations of the module pullbacks are transported along the inverse of the invertible
coefficient comparison `condensedPullbackHom`. -/
lemma IsLisseCoefficientModule.isLocallyFree
    {X : Scheme.{u}}
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLisseCoefficientModule Λ P) :
    IsLocallyFree (condensedRingObj Λ X) P := by
  obtain ⟨U, hU⟩ := hP
  refine ⟨U, fun i ↦ ?_⟩
  let φ := condensedPullbackHom Λ (U.f i)
  have h : Mod.IsFree _ ((Mod.comap (inv φ)).obj
      (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ X)).obj P)) := by
    exact free_of_iso (hU i) ((Mod.extendScalarsIsoComapInv φ).app _)
  exact free_of_comap (inv φ) h

/-- On a quasi-compact quasi-separated scheme, a morphism from a locally free module object
to the colimit of a filtered diagram factors through some stage of the diagram: internal Hom
out of a locally free module object preserves colimits, and the unit object is compact. -/
lemma IsLocallyFree.exists_comp_eq_of_isColimit
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : IsLocallyFree R P)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (c : Cocone D) (hc : IsColimit c) (a : P ⟶ c.pt) :
    ∃ (i : I) (b : P ⟶ D.obj i), b ≫ c.ι.app i = a := by
  let H := Mod.ihom P
  let : PreservesColimitsOfSize.{u + 1, u + 1} H :=
    condensed_locally_free_ihom_preservesColimits R P hP
  let e : (Mod.tensorLeft P).obj (Mod.regular R) ≅ P :=
    (Mod.relativeTensorRightIso P).app (Mod.regular R) ≪≫ (λ_ P)
  let a' := (Mod.ihomAdjunction P).homEquiv _ _ (e.hom ≫ a)
  let ch := H.mapCocone c
  have hch := isColimitOfPreserves H hc
  obtain ⟨i, b, hb⟩ := unitHom_stage X I _ ((Mod.forget R).mapCocone ch)
    (isColimitOfPreserves (Mod.forget R) hch) (η[R] ≫ a'.hom)
  let b' : Mod.regular R ⟶ H.obj (D.obj i) := Mod.regularLift _ b
  have hb' : b' ≫ H.map (c.ι.app i) = a' := by
    apply Mod.regular_hom_ext
    rw [Mod.comp_hom', ← Category.assoc, Mod.one_comp_regularLift]
    exact hb
  refine ⟨i, e.inv ≫ ((Mod.ihomAdjunction P).homEquiv _ _).symm b', ?_⟩
  apply (cancel_epi e.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply ((Mod.ihomAdjunction P).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact hb'
private lemma conjugation_of_mixed_factorization
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C] [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A : C}
    [MonObj R] [MonObj S] [MonObj A] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ A) [IsMonHom g]
    (k : R ⟶ A) [IsMonHom k] (h : f ≫ g = k)
    (M N : Mod C R)
    (b : M ⟶ (Mod.comap f).obj ((Mod.extendScalars f).obj N))
    (ψ : (Mod.extendScalars k).obj M ⟶ (Mod.extendScalars k).obj N)
    (hb : b ≫ Mod.mixedScalarMap f k f k g h h N =
      (Mod.extendRestrictAdjunction k).homEquiv _ _ ψ) :
    let c := Mod.extendScalarsIsoOfEq h.symm ≪≫ Mod.extendScalarsComp f g
    c.hom.app M ≫ (Mod.extendScalars g).map
      (((Mod.extendRestrictAdjunction f).homEquiv _ _).symm b) ≫ c.inv.app N = ψ := by
  dsimp only
  let t := ((Mod.extendRestrictAdjunction f).homEquiv _ _).symm b
  let c := Mod.extendScalarsIsoOfEq h.symm ≪≫ Mod.extendScalarsComp f g
  change c.hom.app M ≫ (Mod.extendScalars g).map t ≫ c.inv.app N = ψ
  apply (cancel_epi (c.inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply ((Mod.extendRestrictAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  apply ((Mod.extendRestrictAdjunction f).homEquiv _ _).injective
  apply Mod.hom_ext
  simp only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom', Mod.comap_map_hom]
  have ht : (Mod.extendUnit f M).hom ≫ t.hom = b.hom := by
    have hh := Equiv.apply_symm_apply ((Mod.extendRestrictAdjunction f).homEquiv _ _) b
    simpa only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
      Mod.comap_map_hom] using congrArg Mod.Hom.hom hh
  have hcunit (P : Mod C R) :
      (Mod.extendUnit f P).hom ≫
        (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom ≫
          (c.inv.app P).hom = (Mod.extendUnit k P).hom := by
    have heq := Adjunction.unit_leftAdjointUniq_hom_app
      (Mod.extendRestrictAdjunction k)
      ((Mod.extendRestrictAdjunction (f ≫ g)).ofNatIsoRight
        (Mod.comapCongr h.symm).symm) P
    have hcomp := Adjunction.unit_leftAdjointUniq_hom_app
      (Mod.extendRestrictAdjunction (f ≫ g))
      (((Mod.extendRestrictAdjunction f).comp (Mod.extendRestrictAdjunction g)).ofNatIsoRight
        (Mod.comapComp f g).symm) P
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_unit_app, scalar_unit] at heq hcomp
    have heq' := congrArg Mod.Hom.hom heq
    have hcomp' := congrArg Mod.Hom.hom hcomp
    change (Mod.extendUnit k P).hom ≫
        ((Mod.extendScalarsIsoOfEq h.symm).hom.app P).hom =
      (Mod.extendUnit (f ≫ g) P).hom ≫ 𝟙 _ at heq'
    change (Mod.extendUnit (f ≫ g) P).hom ≫
        ((Mod.extendScalarsComp f g).hom.app P).hom =
      ((Mod.extendUnit f P).hom ≫
        (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom) ≫ 𝟙 _ at hcomp'
    simp only [Category.comp_id] at heq' hcomp'
    have hh : (Mod.extendUnit k P).hom ≫ (c.hom.app P).hom =
        (Mod.extendUnit f P).hom ≫
          (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom := by
      change (Mod.extendUnit k P).hom ≫
        (((Mod.extendScalarsIsoOfEq h.symm).hom.app P).hom ≫
          ((Mod.extendScalarsComp f g).hom.app P).hom) = _
      rw [← Category.assoc, heq', hcomp']
    rw [← Category.assoc, ← hh, Category.assoc]
    have hi := congrArg Mod.Hom.hom (c.hom_inv_id_app P)
    change (c.hom.app P).hom ≫ (c.inv.app P).hom = 𝟙 _ at hi
    rw [hi]
    exact Category.comp_id _
  have hmix (P : Mod C R) :
      (Mod.extendUnit g ((Mod.extendScalars f).obj P)).hom ≫ (c.inv.app P).hom =
        (Mod.mixedScalarMap f k f k g h h P).hom := by
    have hm : (Mod.extendUnit f P).hom ≫
        (Mod.mixedScalarMap f k f k g h h P).hom = (Mod.extendUnit k P).hom := by
      dsimp only [Mod.mixedScalarMap, Mod.Hom.mk']
      exact Mod.extendUnitHom_extendHom f _
    let q : (Mod.extendScalars f).obj P ⟶
        (Mod.comap g).obj ((Mod.extendScalars k).obj P) :=
      (Mod.extendRestrictAdjunction g).homEquiv _ _ (c.inv.app P)
    let r : (Mod.extendScalars f).obj P ⟶
        (Mod.comap g).obj ((Mod.extendScalars k).obj P) :=
      (Mod.comapId S).inv.app _ ≫
        Mod.mixedScalarMap f k (𝟙 S) g g h (by simp) P
    have hr : r.hom = (Mod.mixedScalarMap f k f k g h h P).hom := by
      change 𝟙 _ ≫ (Mod.mixedScalarMap f k (𝟙 S) g g h (by simp) P).hom = _
      rw [Category.id_comp]
      rfl
    have hqr : q = r := by
      apply ((Mod.extendRestrictAdjunction f).homEquiv _ _).injective
      apply Mod.hom_ext
      simp only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom', Mod.comap_map_hom]
      simpa only [hr, q, Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
        Mod.comap_map_hom] using (hcunit P).trans hm.symm
    simpa only [q, Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
      Mod.comap_map_hom] using (congrArg Mod.Hom.hom hqr).trans hr
  change (Mod.extendUnit f M).hom ≫
      (t.hom ≫ (Mod.extendUnit g ((Mod.extendScalars f).obj N)).hom ≫
        (c.inv.app N).hom) = _
  calc
    _ = b.hom ≫ ((Mod.extendUnit g ((Mod.extendScalars f).obj N)).hom ≫
        (c.inv.app N).hom) := by rw [← Category.assoc, ht]
    _ = b.hom ≫ (Mod.mixedScalarMap f k f k g h h N).hom := congrArg (b.hom ≫ ·) (hmix N)
    _ = (Mod.extendUnit k M).hom ≫ ψ.hom := by
      simpa only [Adjunction.homEquiv_unit, scalar_unit, Mod.comp_hom',
        Mod.comap_map_hom] using congrArg Mod.Hom.hom hb
    _ = _ := by rw [← hcunit M]; simp only [Category.assoc]

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- A morphism of algebraic-closure extensions of two lisse finite-field modules
is obtained at a finite field. This asserts only existence of representatives, not their
comparison or equality relation. -/
theorem exists_lisse_finite_hom_lift [CompactSpace X] [QuasiSeparatedSpace X]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) M)
    (hN : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) N)
    (ψ : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj M ⟶
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F)
      (φ : (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj M ⟶
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj N),
      let c := Mod.extendScalarsIsoOfEq
          (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h).symm ≪≫
        Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
          (padicSubfieldRingObjToPadicAlgCl X ℓ F)
      c.hom.app M ≫
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).map φ ≫
          c.inv.app N = ψ := by
  let : HasZeroMorphisms
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
    inferInstance
  have _ := hN
  let C := (HomologicalComplex.single _ (.up ℤ) 0).obj N
  let I := AsSmall.{u + 1} (Under E)
  let H : I ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E
  let : H.Final := by dsimp only [H]; infer_instance
  let he (i : I) : E ≤ H.obj i := leOfHom (ULift.down i).hom
  let : HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
    inferInstance
  have hc0 : IsColimit (coefficientComplexCocone X ℓ (E := E) (F := E) C H he he) :=
    Classical.choice (nonempty_isColimit_coefficientComplexCocone X ℓ
      (E := E) (F := E) C H he he)
  let : HasColimit (coefficientComplexDiagram X ℓ C H he he) :=
    ⟨⟨coefficientComplexCocone X ℓ (E := E) (F := E) C H he he, hc0⟩⟩
  let c := (HomologicalComplex.eval _ (.up ℤ) 0).mapCocone
    (coefficientComplexCocone X ℓ (E := E) (F := E) C H he he)
  have hc : IsColimit c :=
    isColimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) 0) hc0
  let a := (Mod.extendRestrictAdjunction
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)).homEquiv _ _ ψ
  obtain ⟨i, b, hb⟩ := hM.isLocallyFree.exists_comp_eq_of_isColimit c hc a
  refine ⟨H.obj i, he i,
    ((Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ (he i))).homEquiv _ _).symm b,
    ?_⟩
  exact conjugation_of_mixed_factorization
    (padicSubfieldRingObjMap X ℓ (he i))
    (padicSubfieldRingObjToPadicAlgCl X ℓ (H.obj i))
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)
    (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (he i)) M N b ψ hb

end AlgebraicGeometry.ProEtale
