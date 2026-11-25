/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.RingTheory.Ideal.Quotient.PowTransition
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
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
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Finiteness.Defs
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.CategoryTheory.Limits.Final
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import all WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.RingTheory.Flat.Basic
import all Mathlib.RingTheory.Flat.Tensor
import all Mathlib.LinearAlgebra.TensorProduct.RightExactness
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Linear.FunctorCategory
import all Mathlib.CategoryTheory.Linear.LinearFunctor
import all WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import all Mathlib.CategoryTheory.Limits.Over
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all WeilConjectures.RingTheory.LimitFlatModules
import all Mathlib.RingTheory.Flat.EquationalCriterion
import all Mathlib.RingTheory.TensorProduct.Quotient
import all Mathlib.RingTheory.Ideal.Quotient.Noetherian
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedReductionRestriction
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalQuotientScalarCone
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalFiniteUnderlyingIsoLift
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Quotient and normalized endpoint comparisons for cyclic coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom
  isCommMonObj_condensedRingObj Profinite.isCommMonObj_continuousMapRingObj

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  cyclicLine cyclicLineMap
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

private def cyclicScalarAdjunction (l n : ℕ) [Fact l.Prime] (W : Scheme.{u}) :
    derivedScalars (cyclicMap l n) W ⊣
      (Mod.comap (D := DiagonalAb W) (coefficientMap (cyclicMap l n) W)).mapDerivedCategory := by
  unfold derivedScalars
  exact @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) W)
    (condensedRingObj (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) W) _ _
    (isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) W)
    (isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) W)
    (coefficientMap (cyclicMap l n) W) _

private theorem sheaf_mono_of_app_mono
    {C D : Type*} [Category C] [Category D] (J : GrothendieckTopology C)
    {F G : Sheaf J D} (f : F ⟶ G)
    (h : ∀ V, Mono (((sheafToPresheaf J D).map f).app V)) : Mono f := by
  let (V : Cᵒᵖ) : Mono (((sheafToPresheaf J D).map f).app V) := h V
  have : Mono ((sheafToPresheaf J D).map f) := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf J D).mono_of_mono_map inferInstance

-- Exact pullback and pointwise injectivity require a larger elaboration budget.
private theorem cyclicMap_shortExact (l n : ℕ) [Fact l.Prime] (W : Scheme.{u}) :
    ∃ w : (((l ^ (n + 1) : ℕ) : ℤ) •
        𝟙 (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) W)) ≫
        coefficientMap (cyclicMap l n) W = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  let R := Profinite.continuousMapRingObj.{u} ℤ_[l]
  obtain ⟨w, ⟨hc⟩⟩ := purContinuousCokernel.{u} l (n + 1)
  have hm : Mono (l ^ (n + 1) • 𝟙 R) := by
    apply sheaf_mono_of_app_mono
    intro V
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro a b hab
    apply ULift.ext
    apply ContinuousMap.ext
    intro t
    have h := congrArg (fun z : ULift.{u + 1} C(V.unop, ℤ_[l]) ↦ z.down t) hab
    apply mul_left_cancel₀
      (pow_ne_zero (n + 1) (PadicInt.irreducible_p (p := l)).ne_zero)
    change (l ^ (n + 1)) • a.down t = (l ^ (n + 1)) • b.down t at h
    simpa only [nsmul_eq_mul, Nat.cast_pow] using h
  let q := cyclicMap.{u} l n
  have wq : (l ^ (n + 1) • 𝟙 R) ≫ q = 0 := w
  have : Epi q := epi_of_isColimit_cofork hc
  have hq : (ShortComplex.mk _ _ wq).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ hc }
  let F := upperStarFromPoint W
  have : F.IsLeftAdjoint := by
    unfold F upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ W))).isLeftAdjoint
  have : PreservesFiniteLimits F := by
    dsimp [F]
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have wz : (((l ^ (n + 1) : ℕ) : ℤ) • 𝟙 (F.obj R)) ≫ F.map q = 0 := by
    rw [natCast_zsmul, ← F.map_id, ← F.map_nsmul, ← F.map_comp, wq, F.map_zero]
  refine ⟨wz, ShortComplex.shortExact_of_iso ?_ (hq.map_of_exact F)⟩
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ _ = F.map (l ^ (n + 1) • 𝟙 R) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id, F.map_nsmul, F.map_id,
      natCast_zsmul]
    rfl
  · change 𝟙 _ ≫ F.map q = F.map q ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

private theorem finiteFunctor_iso_lift {A : Type*} [Category A]
    (l n : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (G : A ⥤ DiagonalMod l W)
    (H : A ⥤ Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue l n)))
    (d : G ⋙ diagonalForget l W ≅ H ⋙ cartierForget (diagonalResidue l n) W) :
    ∃ e : G ≅ H ⋙ diagonalFiniteToPadic l n W,
      ∀ X, (diagonalForget l W).map (e.hom.app X) ≫
        (diagonalFiniteForgetIso l n W).inv.app (H.obj X) = d.hom.app X := by
  classical
  have : (diagonalForget l W).Faithful := by unfold diagonalForget; infer_instance
  have hc (X : A) := diagonal_finite_underlying_iso_lift l n W (G.obj X) (H.obj X)
    (d.app X)
  choose t ht _ using hc
  refine ⟨NatIso.ofComponents t ?_, ht⟩
  intro X Y f
  apply (diagonalForget l W).map_injective
  apply (cancel_mono ((diagonalFiniteForgetIso l n W).inv.app (H.obj Y))).1
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [ht]
  have hn := (diagonalFiniteForgetIso l n W).inv.naturality (H.map f)
  change (diagonalForget l W).map ((diagonalFiniteToPadic l n W).map (H.map f)) ≫
    (diagonalFiniteForgetIso l n W).inv.app (H.obj Y) =
    (diagonalFiniteForgetIso l n W).inv.app (H.obj X) ≫
      (cartierForget (diagonalResidue l n) W).map (H.map f) at hn
  dsimp only [CategoryTheory.Functor.comp_map]
  rw [hn, ← Category.assoc, ht]
  exact d.hom.naturality f

private def completedDiscreteRealization (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (eW : CompletedRealization l W) :
    Modules (Profinite.continuousMapRingObj ℤ_[l]) W ⥤ DiagonalMod l W :=
  eW.F.inv ⋙ diagonalCompletedRestriction l W

private instance completedDiscreteRealization_additive (l : ℕ) [Fact l.Prime]
    (W : Scheme.{u}) (eW : CompletedRealization l W) :
    (completedDiscreteRealization l W eW).Additive := by
  have : eW.F.inv.Additive := Functor.additive_of_preserves_binary_products _
  dsimp [completedDiscreteRealization]
  infer_instance

private instance completedDiscreteRealization_limits (l : ℕ) [Fact l.Prime]
    (W : Scheme.{u}) (eW : CompletedRealization l W) :
    PreservesFiniteLimits (completedDiscreteRealization l W eW) := by
  dsimp [completedDiscreteRealization]
  infer_instance

private instance completedDiscreteRealization_colimits (l : ℕ) [Fact l.Prime]
    (W : Scheme.{u}) (eW : CompletedRealization l W) :
    PreservesFiniteColimits (completedDiscreteRealization l W eW) := by
  dsimp [completedDiscreteRealization]
  infer_instance

private def completedDiscreteUnderlying (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (eW : CompletedRealization l W) :
    completedDiscreteRealization l W eW ⋙ diagonalForget l W ≅ Mod.forget _ :=
  Functor.isoWhiskerLeft eW.F.inv eW.underlying.symm ≪≫
    Functor.isoWhiskerRight eW.F.asEquivalence.counitIso (Mod.forget _) ≪≫
      (Mod.forget _).leftUnitor

private def completedDiscreteRealizationIso (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (eW : CompletedRealization l W) :
    eW.F ⋙ completedDiscreteRealization l W eW ≅ diagonalCompletedRestriction l W :=
  Functor.isoWhiskerRight eW.F.asEquivalence.unitIso.symm
      (diagonalCompletedRestriction l W) ≪≫
    (diagonalCompletedRestriction l W).leftUnitor

private theorem completedDiscreteUnderlying_normalization
    (l : ℕ) [Fact l.Prime] (W : Scheme.{u}) (eW : CompletedRealization l W) :
    Functor.whiskerRight (completedDiscreteRealizationIso l W eW).hom
        (diagonalForget l W) ≫ eW.underlying.inv =
      Functor.whiskerLeft eW.F (completedDiscreteUnderlying l W eW).hom := by
  apply NatTrans.ext
  funext X
  have hn := eW.underlying.inv.naturality (eW.F.asEquivalence.unitIso.inv.app X)
  have he : eW.F.map (eW.F.asEquivalence.unitIso.inv.app X) =
      eW.F.asEquivalence.counitIso.hom.app (eW.F.obj X) := by
    apply (cancel_epi (eW.F.asEquivalence.counitIso.inv.app (eW.F.obj X))).1
    exact (eW.F.asEquivalence.counitInv_functor_comp X).trans
      (Iso.inv_hom_id_app eW.F.asEquivalence.counitIso (eW.F.obj X)).symm
  change (diagonalForget l W).map
      ((diagonalCompletedRestriction l W).map (eW.F.asEquivalence.unitIso.inv.app X)) ≫
      eW.underlying.inv.app X =
    eW.underlying.inv.app (eW.F.inv.obj (eW.F.obj X)) ≫
      (Mod.forget _).map (eW.F.asEquivalence.counitIso.hom.app (eW.F.obj X)) ≫ 𝟙 _
  rw [Category.comp_id]
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  rw [he] at hn
  exact hn

private theorem cyclicRestrictionComparison (l n : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    ∃ t : Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y)) ⋙
        completedDiscreteRealization l (diagonalSurface Y) eW ≅
        p.eW.F ⋙ diagonalFiniteToPadic l n (diagonalSurface Y),
      Functor.whiskerRight t.hom (diagonalForget l (diagonalSurface Y)) ≫
          (cyclicFiniteUnderlying l Y n p).hom =
        Functor.whiskerLeft (Mod.comap (coefficientMap (cyclicMap l n)
          (diagonalSurface Y))) (completedDiscreteUnderlying l (diagonalSurface Y) eW).hom := by
  let R : Modules (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1))))
      (diagonalSurface Y) ⥤ Modules (Profinite.continuousMapRingObj ℤ_[l])
      (diagonalSurface Y) := Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y))
  let F := completedDiscreteRealization l (diagonalSurface Y) eW
  let d : R ⋙ F ⋙ diagonalForget l (diagonalSurface Y) ≅
      p.eW.F ⋙ cartierForget (diagonalResidue l n) (diagonalSurface Y) :=
    Functor.isoWhiskerLeft R (completedDiscreteUnderlying l (diagonalSurface Y) eW) ≪≫
      p.eW.underlying.symm
  obtain ⟨e, he⟩ := finiteFunctor_iso_lift l n (diagonalSurface Y) (R ⋙ F) p.eW.F d
  refine ⟨e, ?_⟩
  apply NatTrans.ext
  funext X
  change (diagonalForget l (diagonalSurface Y)).map (e.hom.app X) ≫
      ((diagonalFiniteForgetIso l n (diagonalSurface Y)).inv.app (p.eW.F.obj X) ≫
        p.eW.underlying.hom.app X) = _
  rw [← Category.assoc, he]
  change ((completedDiscreteUnderlying l (diagonalSurface Y) eW).hom.app (R.obj X) ≫
      p.eW.underlying.inv.app X) ≫ p.eW.underlying.hom.app X = _
  erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem exact_triangle_underlying
    {A B D V : Type*} [Category A] [Category B] [Category D] [Category V]
    [Abelian A] [Abelian B] [Abelian D] [Abelian V]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory V]
    (E : A ⥤ B) (J : B ⥤ D) (Z : A ⥤ D) (U : D ⥤ V) (UR : B ⥤ V)
    [E.Additive] [J.Additive] [Z.Additive] [U.Additive] [UR.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]
    (e : E ⋙ J ≅ Z) (b : J ⋙ U ≅ UR) (a : Z ⋙ U ≅ E ⋙ UR)
    (hw : Functor.whiskerRight e.hom U ≫ a.hom = Functor.whiskerLeft E b.hom) :
    let de := (Functor.mapDerivedCategoryCompIso E J) ≪≫
      Functor.mapDerivedCategoryNatIso e
    let db := (Functor.mapDerivedCategoryCompIso J U) ≪≫
      Functor.mapDerivedCategoryNatIso b
    let da := (Functor.mapDerivedCategoryCompIso Z U) ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso E UR).symm
    Functor.whiskerRight de.hom U.mapDerivedCategory ≫ da.hom =
      Functor.whiskerLeft E.mapDerivedCategory db.hom := by
  have hi : Functor.isoWhiskerRight e U ≪≫ a = Functor.isoWhiskerLeft E b := Iso.ext hw
  have hi' := congrArg (fun i ↦ (Functor.mapDerivedCategoryNatIso i).hom) hi
  rw [Functor.mapDerivedCategoryNatIso_trans] at hi'
  apply NatTrans.ext
  funext X
  have hr := congrArg (fun t ↦ t.app X)
    (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e U)
  have hl := congrArg (fun t ↦ t.app X)
    (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft E b)
  have ha := congrArg (fun t ↦ t.app X) (Functor.mapDerivedCategoryCompIso_assoc E J U)
  have hh := congrArg (fun t ↦ t.app X) hi'
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    at hr hl ha hh
  have hr' : U.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso e).hom.app X) ≫
        (Functor.mapDerivedCategoryCompIso Z U).hom.app X =
      (Functor.mapDerivedCategoryCompIso (E ⋙ J) U).hom.app X ≫
        (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e U)).hom.app X := by
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (E ⋙ J) U).inv.app X)).1
    rw [← Category.assoc, ← hr, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      Iso.inv_hom_id_app_assoc]
  have ha' : U.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso E J).hom.app X) ≫
        (Functor.mapDerivedCategoryCompIso (E ⋙ J) U).hom.app X ≫
        (Functor.mapDerivedCategoryCompIso E (J ⋙ U)).inv.app X =
      (Functor.mapDerivedCategoryCompIso J U).hom.app (E.mapDerivedCategory.obj X) := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso J U).inv.app
      (E.mapDerivedCategory.obj X))).1
    rw [Category.assoc, Category.assoc, ha, Iso.hom_inv_id_app_assoc,
      ← U.mapDerivedCategory.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Iso.hom_inv_id_app]
    rfl
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr', reassoc_of% hh, hl, reassoc_of% ha']

private theorem exact_composite_underlying
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) (F : B ⥤ C) (U : C ⥤ D)
    [E.Additive] [F.Additive] [U.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (X : DerivedCategory A) :
    U.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso E F).inv.app X) ≫
      (Functor.mapDerivedCategoryCompIso F U).hom.app (E.mapDerivedCategory.obj X) ≫
      (Functor.mapDerivedCategoryCompIso E (F ⋙ U)).hom.app X =
    (Functor.mapDerivedCategoryCompIso (E ⋙ F) U).hom.app X := by
  have ha := congrArg (fun t ↦ t.app X) (Functor.mapDerivedCategoryCompIso_assoc E F U)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ha
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (E ⋙ F) U).inv.app X)).1
  rw [← Category.assoc, ← ha]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

private theorem exact_triangle_underlying_inv_app
    {A B D V : Type*} [Category A] [Category B] [Category D] [Category V]
    [Abelian A] [Abelian B] [Abelian D] [Abelian V]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory V]
    (E : A ⥤ B) (J : B ⥤ D) (Z : A ⥤ D) (U : D ⥤ V) (UR : B ⥤ V)
    [E.Additive] [J.Additive] [Z.Additive] [U.Additive] [UR.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]
    (e : E ⋙ J ≅ Z) (b : J ⋙ U ≅ UR) (a : Z ⋙ U ≅ E ⋙ UR)
    (hw : Functor.whiskerRight e.hom U ≫ a.hom = Functor.whiskerLeft E b.hom)
    (X : DerivedCategory A) :
    let de := (Functor.mapDerivedCategoryCompIso E J) ≪≫
      Functor.mapDerivedCategoryNatIso e
    let db := (Functor.mapDerivedCategoryCompIso J U) ≪≫
      Functor.mapDerivedCategoryNatIso b
    let da := (Functor.mapDerivedCategoryCompIso Z U) ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso E UR).symm
    U.mapDerivedCategory.map (de.inv.app X) ≫ db.hom.app (E.mapDerivedCategory.obj X) =
      da.hom.app X := by
  let de := (Functor.mapDerivedCategoryCompIso E J) ≪≫
    Functor.mapDerivedCategoryNatIso e
  let db := (Functor.mapDerivedCategoryCompIso J U) ≪≫
    Functor.mapDerivedCategoryNatIso b
  let da := (Functor.mapDerivedCategoryCompIso Z U) ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso E UR).symm
  have hi := exact_triangle_underlying E J Z U UR e b a hw
  have hiX := NatTrans.congr_app hi X
  dsimp only [de, db, da, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at hiX ⊢
  apply (cancel_epi (U.mapDerivedCategory.map (de.hom.app X))).1
  rw [← Category.assoc, ← U.mapDerivedCategory.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact hiX.symm

private theorem exact_triangle_underlying_right_inv_app
    {A B D V : Type*} [Category A] [Category B] [Category D] [Category V]
    [Abelian A] [Abelian B] [Abelian D] [Abelian V]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory V]
    (E : A ⥤ B) (J : B ⥤ D) (Z : A ⥤ D) (U : D ⥤ V) (UR : B ⥤ V)
    [E.Additive] [J.Additive] [Z.Additive] [U.Additive] [UR.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]
    (e : E ⋙ J ≅ Z) (b : J ⋙ U ≅ UR) (a : Z ⋙ U ≅ E ⋙ UR)
    (hw : Functor.whiskerRight e.hom U ≫ a.hom = Functor.whiskerLeft E b.hom)
    (X : DerivedCategory A) :
    let de := (Functor.mapDerivedCategoryCompIso E J) ≪≫
      Functor.mapDerivedCategoryNatIso e
    let db := (Functor.mapDerivedCategoryCompIso J U) ≪≫
      Functor.mapDerivedCategoryNatIso b
    U.mapDerivedCategory.map (de.hom.app X) ≫
      (Functor.mapDerivedCategoryCompIso Z U).hom.app X ≫
      (Functor.mapDerivedCategoryNatIso a).hom.app X =
      db.hom.app (E.mapDerivedCategory.obj X) ≫
        (Functor.mapDerivedCategoryCompIso E UR).hom.app X := by
  let de := (Functor.mapDerivedCategoryCompIso E J) ≪≫
    Functor.mapDerivedCategoryNatIso e
  let db := (Functor.mapDerivedCategoryCompIso J U) ≪≫
    Functor.mapDerivedCategoryNatIso b
  let da := (Functor.mapDerivedCategoryCompIso Z U) ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso E UR).symm
  have hi := exact_triangle_underlying E J Z U UR e b a hw
  have hiX := NatTrans.congr_app hi X
  dsimp only [de, db, da, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at hiX ⊢
  have h := congrArg (fun f ↦ f ≫ (Functor.mapDerivedCategoryCompIso E UR).hom.app X) hiX
  rw [Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] at h
  exact h

private theorem quotient_unit_composite
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ A) (E : A ⥤ B) (G : B ⥤ C) (Z : A ⥤ C)
    (L : B ⥤ D) (R : D ⥤ B) (H : D ⥤ C)
    (d : E ⋙ G ≅ Z) (b : Q ⋙ E ≅ E ⋙ L ⋙ R) (t : R ⋙ G ≅ H)
    (η : 𝟭 B ⟶ L ⋙ R) (m : 𝟭 A ⟶ Q)
    (hb : ∀ X, E.map (m.app X) ≫ b.hom.app X = η.app (E.obj X)) (X : A) :
    let a := Functor.isoWhiskerLeft Q d.symm ≪≫ Functor.isoWhiskerRight b G ≪≫
      Functor.isoWhiskerLeft (E ⋙ L) t
    Z.map (m.app X) ≫ a.hom.app X =
      d.inv.app X ≫ G.map (η.app (E.obj X)) ≫ t.hom.app (L.obj (E.obj X)) := by
  have hn := d.inv.naturality (m.app X)
  dsimp only [Functor.comp_map] at hn
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp_assoc, hb]
  rfl

private theorem underlying_glue
    {C : Type*} [Category C] {A B D E F G H I J K : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (i : E ⟶ F)
    (j : F ⟶ G) (k : G ⟶ H) (m : H ⟶ I)
    (o : E ⟶ H) (p : D ⟶ J) (q : B ⟶ K) (r : J ⟶ I)
    (z : A ⟶ K) (v : K ⟶ J)
    (hi : i ≫ j ≫ k = o) (hh : h ≫ o ≫ m = p ≫ r)
    (hn : g ≫ p = q ≫ v) (hf : f ≫ q = z) :
    f ≫ g ≫ h ≫ i ≫ j ≫ k ≫ m = (z ≫ v ≫ r) := by
  rw [reassoc_of% hi, hh, reassoc_of% hn, ← Category.assoc, hf]

-- Resolving comparison elaborates several nested derived functors.
private theorem scalarCone_extension_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (r : ℕ)
    (w : ((r : ℤ) • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact) :
    ∃ e : diagonalScalarCone (Mod C R) r ≅
        (Mod.extendScalars φ).leftDerivedFunctor ⋙ (Mod.comap (D := C) φ).mapDerivedCategory,
      ∀ X, (diagonalScalarConeUnit (Mod C R) r).app X ≫ e.hom.app X =
        (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app X := by
  let A := Mod C R
  let L := (Mod.extendScalars φ).leftDerivedFunctor
  let U := (Mod.comap (D := C) φ).mapDerivedCategory
  let E := (Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)
  let V := (Mod.comap (D := C) φ).mapHomologicalComplex (.up ℤ)
  let T := E ⋙ V ⋙ DerivedCategory.Q
  let a := Mod.KFlatScalarTower.computationCounit φ
  let α : DerivedCategory.Q ⋙ (L ⋙ U) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight a U ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft E (Mod.comap (D := C) φ).mapDerivedCategoryFactors.hom
  let ν : 𝟭 (CochainComplex A ℤ) ⟶ E ⋙ V :=
    { app P := Mod.extendUnitComplexHom φ P
      naturality P Q f := by
        simpa only [Mod.extendUnitComplexHom_eq] using
          ((Mod.extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.naturality f }
  let SC (P : CochainComplex A ℤ) := ShortComplex.mk (r • 𝟙 P) (ν.app P) (by
    apply HomologicalComplex.hom_ext
    intro i
    change (r • 𝟙 (P.X i)) ≫ Mod.extendUnit φ (P.X i) = 0
    simpa only [natCast_zsmul] using Mod.zsmul_comp_extendUnit (r : ℤ) w (P.X i))
  let c : diagonalScalarConeComplex A r ⟶ E ⋙ V :=
    { app P := CochainComplex.mappingCone.descShortComplex (SC P)
      naturality P Q f := by
        let t : SC P ⟶ SC Q :=
          { τ₁ := f, τ₂ := f, τ₃ := (E ⋙ V).map f
            comm₁₂ := by
              simp only [SC, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
                Category.id_comp, Category.comp_id]
            comm₂₃ := ν.naturality f }
        exact CochainComplex.mappingCone.map_descShortComplex (SC P) (SC Q) t }
  let β : DerivedCategory.Q ⋙ diagonalScalarCone A r ⟶ T :=
    (diagonalScalarConeFactors A r).hom ≫ Functor.whiskerRight c DerivedCategory.Q
  let good : CochainComplex A ℤ → Prop := fun P ↦
    (∀ i, ObjectProperty.flat (P.X i)) ∧
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P
  have res (K : CochainComplex A ℤ) :
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p := by
    obtain ⟨P, p, hp, hf, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
    exact ⟨P, p, ⟨hf, hk⟩, hp⟩
  have hα (P : CochainComplex A ℤ) (hP : good P) : IsIso (α.app P) := by
    have : IsIso ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj P)) :=
      (Mod.extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP.2
    have : IsIso (a.app P) := by
      dsimp only [a, Mod.KFlatScalarTower.computationCounit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    dsimp only [α, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp]
    infer_instance
  have hβ (P : CochainComplex A ℤ) (hP : good P) : IsIso (β.app P) := by
    have hs : (SC P).ShortExact := by
      simpa only [SC, ν, E, V, Functor.mapHomologicalComplex, Functor.comp_obj, Functor.comp_map,
        natCast_zsmul] using
        Mod.shortExact_extendUnitComplexHom (r : ℤ) w hφ P hP.1
    have : QuasiIso (c.app P) := CochainComplex.mappingCone.quasiIso_descShortComplex hs
    change IsIso ((diagonalScalarConeFactors A r).hom.app P ≫
      DerivedCategory.Q.map (c.app P))
    infer_instance
  obtain ⟨e, he⟩ := CategoryTheory.ConstantCompletion.resolving_comparison_iso
    (diagonalScalarCone A r) (L ⋙ U) T good res β α hβ hα
  let η := (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit
  have hη (P : CochainComplex A ℤ) :
      η.app (DerivedCategory.Q.obj P) ≫ α.app P = DerivedCategory.Q.map (ν.app P) := by
    dsimp only [α, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp]
    rw [← Category.assoc, Mod.KFlatScalarTower.computationCounit_unit_inv,
      Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [← Mod.extendUnitComplexHom_eq]
  refine ⟨e, fun X ↦ ?_⟩
  have h : diagonalScalarConeUnit A r ≫ e.hom = η := by
    apply CategoryTheory.ConstantCompletion.resolving_nat_ext good res
    intro P hP
    have := hα P hP
    apply (cancel_mono (α.app P)).1
    change ((diagonalScalarConeUnit A r).app (DerivedCategory.Q.obj P) ≫
      e.hom.app (DerivedCategory.Q.obj P)) ≫ α.app P = _
    rw [Category.assoc, he P hP, hη]
    change (diagonalScalarConeUnit A r).app (DerivedCategory.Q.obj P) ≫
      ((diagonalScalarConeFactors A r).hom.app P ≫ DerivedCategory.Q.map (c.app P)) = _
    rw [← Category.assoc, diagonalScalarConeUnit_factors, ← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map (CochainComplex.mappingCone.inr_descShortComplex (SC P))
  exact congrArg (fun τ ↦ τ.app X) h

private theorem comp_three_eq
    {C : Type*} [Category C] {A B D E F : C}
    {f : A ⟶ B} {a : B ⟶ D} {b : D ⟶ E} {c : E ⟶ F}
    {g : A ⟶ D} {h : A ⟶ E} {i : A ⟶ F}
    (ha : f ≫ a = g) (hb : g ≫ b = h) (hc : h ≫ c = i) :
    f ≫ (a ≫ b ≫ c) = i := by
  rw [← Category.assoc, ha, ← Category.assoc, hb, hc]

-- The reduction comparison computes exact realization on regular resolutions.
private theorem completedScalarComparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y))
    (M : DiagonalCompletedReduction l (diagonalSurface Y)) :
    ∃ b : cyclicCompletedQuotient l (diagonalSurface Y) M n ⋙
        eW.F.mapDerivedCategory ≅
      eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y) ⋙
        (Mod.comap (D := DiagonalAb (diagonalSurface Y))
          (coefficientMap (cyclicMap l n) (diagonalSurface Y))).mapDerivedCategory,
      ∀ X, eW.F.mapDerivedCategory.map ((M.unit n).app X) ≫ b.hom.app X =
        (cyclicScalarAdjunction l n (diagonalSurface Y)).unit.app
            (eW.F.mapDerivedCategory.obj X) := by
  let W := diagonalSurface Y
  let E := eW.F
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : E.inv.Additive := Functor.additive_of_preserves_binary_products E.inv
  have : IsGrothendieckAbelian.{u + 1}
      (ℕᵒᵖ ⥤ Modules (Profinite.continuousMapRingObj ℤ_[l]) W) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck _
  let resA := completedRegularResolution l W
  have : E.asEquivalence.symm.functor.Additive := ‹E.inv.Additive›
  have : E.asEquivalence.symm.inverse.Additive := ‹E.Additive›
  let resB := transportRegularResolution E.asEquivalence.symm l resA
  obtain ⟨N, hN⟩ := normalizedReductionExists l resB
  obtain ⟨a, ha⟩ := reductionComparison l E M N resA
    (reduction_computes_regular l M.derived resA) hN n
  obtain ⟨b, hb⟩ := diagonal_quotient_scalar_cone l N resB n
  obtain ⟨w, hw⟩ := cyclicMap_shortExact l n W
  obtain ⟨c, hc⟩ := @scalarCone_extension_comparison
    (DiagonalAb W) _ _ _ _ _ _ _ _
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) W)
    (condensedRingObj (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) W) _ _
    (isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) W)
    (isCommMonObj_condensedRingObj (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) W)
    (coefficientMap (cyclicMap l n) W) _ (l ^ (n + 1)) w hw
  refine ⟨a ≪≫ Functor.isoWhiskerLeft E.mapDerivedCategory (b ≪≫ c), ?_⟩
  intro X
  change E.mapDerivedCategory.map ((M.unit n).app X) ≫
    (a.hom.app X ≫ b.hom.app (E.mapDerivedCategory.obj X) ≫
      c.hom.app (E.mapDerivedCategory.obj X)) = _
  exact comp_three_eq (ha X) (hb (E.mapDerivedCategory.obj X))
    (hc (E.mapDerivedCategory.obj X))

attribute [local irreducible] Functor.mapDerivedCategory in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The normalized unit square involves several exact-derived coherence isomorphisms.
/-- The derived scalar quotient and any normalized simultaneous completed quotient
have the same underlying quotient unit, naturally on every derived input.

Source: coefficient changes (1), scalar quotient; diagonal limit (3), normalized
completed reductions (blueprint: lem-diagonal-cyclic-quotient-comparison).

Proof: the completed unit normalization identifies the coefficient projection with
the continuous cyclic reduction. Its kernel is generated by l^(n+1), and its
projection is epic. The ordinary extension/restriction composite and the level-n
ordinary reduction are therefore cokernels of the same multiplication map.
The unique cokernel comparisons are natural. Resolve completed complexes by
flat-term K-flat complexes. Both quotient constructions preserve quasi-isomorphisms
between these resolutions: their underlying complexes compute the cone of the
same multiplication map. Exact realization and forgetting retain that property.
The pointwise left-derived universal properties extend the ordinary comparisons
to all derived objects and make them invertible there. The scalar adjunction unit
and M.normalization both localize the ordinary quotient projection. Their equality
on resolving complexes descends through localization to the displayed unit square.
This uses no flatness of the cyclic coefficient map. The exponent n+1 is positive
also for n=0; over the empty scheme all constructions are the zero functors. -/
theorem diagonalCyclicQuotient_comparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n)
    (M : DiagonalCompletedReduction l (diagonalSurface Y)) :
    ∃ e : cyclicEvaluationFunctor l Y n eW p ≅
        cyclicCompletedQuotient l (diagonalSurface Y) M n ⋙
          cyclicDiscreteRestriction l (diagonalSurface Y),
      ∀ X : DerivedCategory (DiagonalCompleted l (diagonalSurface Y)),
        (cyclicEvaluationAugmentation l Y n eW p).app X ≫
            (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map (e.hom.app X) =
          (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
            ((cyclicDiscreteRestriction l (diagonalSurface Y)).map ((M.unit n).app X)) := by
  let W := diagonalSurface Y
  let E := eW.F
  let G := completedDiscreteRealization l W eW
  let Z := diagonalCompletedRestriction l W
  let U := diagonalForget l W
  let V := Mod.forget (D := DiagonalAb W)
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) W)
  let R := Mod.comap (D := DiagonalAb W) (coefficientMap (cyclicMap l n) W)
  let L := derivedScalars (cyclicMap l n) W
  let H := p.eW.F ⋙ diagonalFiniteToPadic l n W
  let Q := cyclicCompletedQuotient l W M n
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : H.Additive := by dsimp [H]; infer_instance
  have : PreservesFiniteLimits H := by dsimp [H]; infer_instance
  have : PreservesFiniteColimits H := by dsimp [H]; infer_instance
  let d : E.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ Z.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso E G) ≪≫
      Functor.mapDerivedCategoryNatIso (completedDiscreteRealizationIso l W eW)
  let g : G.mapDerivedCategory ⋙ U.mapDerivedCategory ≅ V.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso G U) ≪≫
      Functor.mapDerivedCategoryNatIso (completedDiscreteUnderlying l W eW)
  obtain ⟨t, ht⟩ := cyclicRestrictionComparison l n Y eW p
  let dt : R.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso R G) ≪≫ Functor.mapDerivedCategoryNatIso t
  let dh : H.mapDerivedCategory ≅ p.eW.F.mapDerivedCategory ⋙
      (diagonalFiniteToPadic l n W).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm
  obtain ⟨b, hb⟩ := completedScalarComparison l Y n eW M
  let a : Q ⋙ Z.mapDerivedCategory ≅ cyclicEvaluationFunctor l Y n eW p :=
    Functor.isoWhiskerLeft Q d.symm ≪≫
      Functor.isoWhiskerRight b G.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (E.mapDerivedCategory ⋙ L) (dt ≪≫ dh)
  have ha (X : DerivedCategory (DiagonalCompleted l W)) :
      U.mapDerivedCategory.map (Z.mapDerivedCategory.map ((M.unit n).app X)) ≫
        U.mapDerivedCategory.map (a.hom.app X) =
      (cyclicEvaluationAugmentation l Y n eW p).app X := by
    have hc := exact_composite_underlying p.eW.F (diagonalFiniteToPadic l n W) U
      (L.obj (E.mapDerivedCategory.obj X))
    let η := (cyclicScalarAdjunction l n W).unit
    have hunit : Z.mapDerivedCategory.map ((M.unit n).app X) ≫ a.hom.app X =
        d.inv.app X ≫ G.mapDerivedCategory.map (η.app (E.mapDerivedCategory.obj X)) ≫
          dt.hom.app (L.obj (E.mapDerivedCategory.obj X)) ≫
            dh.hom.app (L.obj (E.mapDerivedCategory.obj X)) := by
      simpa only [a, Iso.trans_hom, NatTrans.comp_app] using
        (quotient_unit_composite Q E.mapDerivedCategory G.mapDerivedCategory
          Z.mapDerivedCategory L R.mapDerivedCategory
          (p.eW.F.mapDerivedCategory ⋙ (diagonalFiniteToPadic l n W).mapDerivedCategory)
          d b (dt ≪≫ dh) η (M.unit n) hb X)
    erw [← U.mapDerivedCategory.map_comp, hunit]
    apply (cancel_mono ((cyclicEvaluationUnderlying l Y n eW p).hom.app X)).1
    simp only [cyclicEvaluationAugmentation, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    change U.mapDerivedCategory.map (d.inv.app X) ≫
        U.mapDerivedCategory.map (G.mapDerivedCategory.map
          (η.app (E.mapDerivedCategory.obj X))) ≫
        U.mapDerivedCategory.map (dt.hom.app (L.obj (E.mapDerivedCategory.obj X))) ≫
        U.mapDerivedCategory.map (dh.hom.app (L.obj (E.mapDerivedCategory.obj X))) ≫
        (Functor.mapDerivedCategoryCompIso (diagonalFiniteToPadic l n W) U).hom.app
          (p.eW.F.mapDerivedCategory.obj (L.obj (E.mapDerivedCategory.obj X))) ≫
        (Functor.mapDerivedCategoryCompIso p.eW.F
          (diagonalFiniteToPadic l n W ⋙ U)).hom.app
          (L.obj (E.mapDerivedCategory.obj X)) ≫
        (Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)).hom.app
          (L.obj (E.mapDerivedCategory.obj X)) =
      ((Functor.mapDerivedCategoryCompIso Z U).hom.app X ≫
        (Functor.mapDerivedCategoryNatIso eW.underlying.symm).hom.app X ≫
          (Functor.mapDerivedCategoryCompIso E V).inv.app X) ≫
        (V.mapDerivedCategory.map (η.app (E.mapDerivedCategory.obj X)) ≫ 𝟙 _ ≫
          ((Functor.mapDerivedCategoryCompIso R V).hom.app
            (L.obj (E.mapDerivedCategory.obj X)) ≫ 𝟙 _)) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    have htX' : U.mapDerivedCategory.map (dt.hom.app
          (L.obj (E.mapDerivedCategory.obj X))) ≫
        (Functor.mapDerivedCategoryCompIso H U).hom.app
          (L.obj (E.mapDerivedCategory.obj X)) ≫
        (Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)).hom.app
          (L.obj (E.mapDerivedCategory.obj X)) =
      g.hom.app (R.mapDerivedCategory.obj (L.obj (E.mapDerivedCategory.obj X))) ≫
        (Functor.mapDerivedCategoryCompIso R (Mod.forget _)).hom.app
          (L.obj (E.mapDerivedCategory.obj X)) := by
      simpa only [dt, g, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        CategoryTheory.Functor.map_comp] using
        (exact_triangle_underlying_right_inv_app R G H U (Mod.forget _) t
          (completedDiscreteUnderlying l W eW) (cyclicFiniteUnderlying l Y n p) ht
          (L.obj (E.mapDerivedCategory.obj X)))
    have hgn := g.hom.naturality (η.app (E.mapDerivedCategory.obj X))
    dsimp only [CategoryTheory.Functor.comp_map] at hgn
    have hh : U.mapDerivedCategory.map (d.inv.app X) ≫
        g.hom.app (E.mapDerivedCategory.obj X) =
        (Functor.mapDerivedCategoryCompIso Z U).hom.app X ≫
          (Functor.mapDerivedCategoryNatIso eW.underlying.symm).hom.app X ≫
            (Functor.mapDerivedCategoryCompIso E V).inv.app X := by
      simpa only [d, g, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app] using
        (exact_triangle_underlying_inv_app E G Z U V
          (completedDiscreteRealizationIso l W eW)
          (completedDiscreteUnderlying l W eW) eW.underlying.symm
          (completedDiscreteUnderlying_normalization l W eW) X)
    simpa only [dh, V, Iso.symm_hom, Category.assoc] using
      (underlying_glue (hi := hc) (hh := htX') (hn := hgn) (hf := hh))
  refine ⟨a.symm, fun X ↦ ?_⟩
  change (cyclicEvaluationAugmentation l Y n eW p).app X ≫
      U.mapDerivedCategory.map (a.inv.app X) = _
  erw [← ha X, Category.assoc, ← U.mapDerivedCategory.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
