/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
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
import all WeilConjectures.Algebra.Homology.SixFunctors.FlatScalarCyclicResolution
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompletionCoefficientTransportCore
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import Mathlib.Algebra.Ring.TransferInstance

/-! # Finite reduction and completed scalar restriction

(blueprint: lem-sfb-diagonal-completed-reduction-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.ProEtale

private theorem normalizedReductionExists
    {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] (ℓ : ℕ)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p) :
    ∃ M : DiagonalCompletedReductionData ℓ A,
      ∀ P : CochainComplex A ℤ,
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
          IsIso (M.derived.ε.app P) := by
  let O := reductionPresentation ℓ (𝟭 A)
  let good : CochainComplex A ℤ → Prop := fun P ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))
  obtain ⟨T, β, hu, hp, ht, hc⟩ := cochainDerivedFullExists O.E good res (by
    intro P P' f hf hP hP'
    let : QuasiIso f := hf
    exact reductionTower_quasiIso ℓ (𝟭 A) O f hP hP')
  let D : DiagonalDerivedReduction ℓ (𝟭 A) :=
    { ordinary := O, T := T, ε := β, universal := hu, pointwise := hp,
      triangulated := ht }
  let G : A ⥤ (ℕᵒᵖ ⥤ A) := Functor.const ℕᵒᵖ
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let η : G ⟶ O.E :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ (O.π n).app M)
        (fun n ↦ (Category.id_comp _).trans (O.transition n M).symm)
      naturality := fun M N f ↦ by
        ext n
        exact (O.π n.unop).naturality f }
  have units (n : ℕ) : ∃ unit : 𝟭 (DerivedCategory A) ⟶
      T ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory,
      ∀ P : CochainComplex A ℤ,
        unit.app (DerivedCategory.Q.obj P) ≫
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map (β.app P) ≫
          ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app
            ((O.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P) := by
    let E := (evaluation ℕᵒᵖ A).obj (op n)
    let ν : 𝟭 (CochainComplex A ℤ) ⟶
        G.mapHomologicalComplex (.up ℤ) ⋙ E.mapHomologicalComplex (.up ℤ) :=
      { app := fun P ↦ 𝟙 P }
    have : T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) := hu
    obtain ⟨unit, hunit⟩ := CategoryTheory.ConstantCompletion.derived_tower_unit
      DerivedCategory.Q DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      ν (NatTrans.mapHomologicalComplex η (.up ℤ))
      G.mapDerivedCategory T E.mapDerivedCategory G.mapDerivedCategoryFactors β
      E.mapDerivedCategoryFactors.inv
    refine ⟨unit, fun P ↦ ?_⟩
    have h := hunit P
    have hπ : ν.app P ≫ (E.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P) =
        (NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P := by
      ext i
      exact Category.id_comp _
    rw [hπ] at h
    change unit.app (DerivedCategory.Q.obj P) ≫ E.mapDerivedCategory.map (β.app P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (O.π n) (.up ℤ)).app P) ≫
        E.mapDerivedCategoryFactors.inv.app
          ((O.E.mapHomologicalComplex (.up ℤ)).obj P) at h
    rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  choose unit hunit using units
  exact ⟨{ derived := D, unit := unit, normalization := fun P n ↦ hunit n P }, hc⟩

private theorem ordinaryReductionComparison
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    (ℓ : ℕ) (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (O : DiagonalReductionPresentation ℓ (𝟭 A))
    (P : DiagonalReductionPresentation ℓ (𝟭 B)) (n : ℕ) :
    ∃ e : O.E ⋙ (evaluation ℕᵒᵖ A).obj (op n) ⋙ F ≅
        F ⋙ P.E ⋙ (evaluation ℕᵒᵖ B).obj (op n),
      ∀ X : A, F.map ((O.π n).app X) ≫ e.hom.app X = (P.π n).app (F.obj X) := by
  have hc (X : A) : IsColimit (CokernelCofork.ofπ (F.map ((O.π n).app X))
      (show (ℓ ^ (n + 1) • 𝟙 (F.obj X)) ≫ F.map ((O.π n).app X) = 0 by
        rw [← F.map_id, ← F.map_nsmul, ← F.map_comp]
        exact (congrArg F.map (O.zero n X)).trans (F.map_zero _ _))) := by
    have h := isColimitCoforkMapOfIsColimit' F (O.zero n X) (O.quotient n X)
    have ht (f : F.obj X ⟶ F.obj X)
        (w : f ≫ F.map ((O.π n).app X) = 0)
        (hh : IsColimit (CokernelCofork.ofπ (F.map ((O.π n).app X)) w))
        (hf : f = ℓ ^ (n + 1) • 𝟙 (F.obj X)) :
        IsColimit (CokernelCofork.ofπ (F.map ((O.π n).app X))
          (show (ℓ ^ (n + 1) • 𝟙 (F.obj X)) ≫ F.map ((O.π n).app X) = 0 by
            rw [← hf]; exact w)) := by
      subst f
      exact hh
    exact ht _ _ h (by rw [F.map_nsmul, F.map_id]; rfl)
  let e (X : A) := (hc X).coconePointUniqueUpToIso (P.quotient n (F.obj X))
  have he (X : A) : F.map ((O.π n).app X) ≫ (e X).hom = (P.π n).app (F.obj X) :=
    (hc X).comp_coconePointUniqueUpToIso_hom (P.quotient n (F.obj X)) WalkingParallelPair.one
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro X Y f
  have : Epi (F.map ((O.π n).app X)) := Cofork.IsColimit.epi (hc X)
  apply (cancel_epi (F.map ((O.π n).app X))).1
  have hO : (O.π n).app X ≫ (O.E.map f).app (op n) = f ≫ (O.π n).app Y :=
    ((O.π n).naturality f).symm
  change F.map ((O.π n).app X) ≫
      (F.map ((O.E.map f).app (op n)) ≫ (e Y).hom) =
    F.map ((O.π n).app X) ≫ ((e X).hom ≫ (P.E.map (F.map f)).app (op n))
  rw [← F.map_comp_assoc, hO, F.map_comp_assoc, he, ← Category.assoc, he]
  exact (P.π n).naturality (F.map f)

private theorem reductionComparison
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : DiagonalCompletedReductionData ℓ A) (N : DiagonalCompletedReductionData ℓ B)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p)
    (hM : ∀ P : CochainComplex A ℤ,
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
        IsIso (M.derived.ε.app P))
    (hN : ∀ P : CochainComplex B ℤ,
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
        IsIso (N.derived.ε.app P)) (n : ℕ) :
    let C := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
    let E := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
    ∃ α : M.derived.T ⋙ C ⋙ F.mapDerivedCategory ≅
        F.mapDerivedCategory ⋙ N.derived.T ⋙ E,
      ∀ P : DerivedCategory A,
        F.mapDerivedCategory.map ((M.unit n).app P) ≫ α.hom.app P =
          (N.unit n).app (F.mapDerivedCategory.obj P) := by
  let C := (evaluation ℕᵒᵖ A).obj (op n)
  let E := (evaluation ℕᵒᵖ B).obj (op n)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Oc := M.derived.ordinary.E.mapHomologicalComplex (.up ℤ)
  let Vc := N.derived.ordinary.E.mapHomologicalComplex (.up ℤ)
  let Cc := C.mapHomologicalComplex (.up ℤ)
  let β : DerivedCategory.Q ⋙ (C.mapDerivedCategory ⋙ F.mapDerivedCategory) ⟶
      (C ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight C.mapDerivedCategoryFactors.hom F.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Cc F.mapDerivedCategoryFactors.hom
  let ε : DerivedCategory.Q ⋙ (N.derived.T ⋙ E.mapDerivedCategory) ⟶
      (N.derived.ordinary.E ⋙ E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight N.derived.ε E.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Vc E.mapDerivedCategoryFactors.hom
  obtain ⟨e, he⟩ := ordinaryReductionComparison ℓ F M.derived.ordinary N.derived.ordinary n
  let γ : Oc ⋙ (C ⋙ F).mapHomologicalComplex (.up ℤ) ≅
      Fc ⋙ (N.derived.ordinary.E ⋙ E).mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex e (.up ℤ)
  let good : CochainComplex A ℤ → Prop := fun P ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))
  have hF (P : CochainComplex A ℤ) (hP : good P) :
      ∀ (m : ℕ) (i : ℤ), Mono (ℓ ^ (m + 1) • 𝟙 ((Fc.obj P).X i)) := by
    intro m i
    have := hP m i
    have h := F.map_mono (ℓ ^ (m + 1) • 𝟙 (P.X i))
    change Mono (ℓ ^ (m + 1) • 𝟙 (F.obj (P.X i)))
    simpa only [F.map_nsmul, F.map_id] using h
  obtain ⟨α, hα, _⟩ := CategoryTheory.ConstantCompletion.resolving_square_iso
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    Oc Fc ((C ⋙ F).mapHomologicalComplex (.up ℤ))
    ((N.derived.ordinary.E ⋙ E).mapHomologicalComplex (.up ℤ))
    M.derived.T F.mapDerivedCategory (C.mapDerivedCategory ⋙ F.mapDerivedCategory)
    (N.derived.T ⋙ E.mapDerivedCategory)
    M.derived.ε β γ F.mapDerivedCategoryFactors.hom ε good res hM
    (fun P _ ↦ by dsimp [β]; infer_instance)
    (fun P _ ↦ inferInstance)
    (fun P hP ↦ by
      have := hN (Fc.obj P) (hF P hP)
      dsimp [ε]
      infer_instance)
  let τ : F.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙
      N.derived.T ⋙ E.mapDerivedCategory :=
    F.mapDerivedCategory.leftUnitor.inv ≫
      Functor.whiskerRight (M.unit n) F.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫ α.hom
  let σ : F.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙
      N.derived.T ⋙ E.mapDerivedCategory :=
    F.mapDerivedCategory.rightUnitor.inv ≫
      Functor.whiskerLeft F.mapDerivedCategory (N.unit n)
  have hτσ : τ = σ := by
    apply CategoryTheory.ConstantCompletion.resolving_nat_ext good res
    intro P hP
    have := hN (Fc.obj P) (hF P hP)
    let z := (N.derived.T ⋙ E.mapDerivedCategory).map
        (F.mapDerivedCategoryFactors.hom.app P) ≫ ε.app (Fc.obj P)
    have : IsIso z := by dsimp [z, ε]; infer_instance
    apply (cancel_mono z).1
    dsimp only [τ, σ, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.associator_hom_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp]
    change (F.mapDerivedCategory.map ((M.unit n).app (DerivedCategory.Q.obj P)) ≫
        α.hom.app (DerivedCategory.Q.obj P)) ≫ z =
      (N.unit n).app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫ z
    have hcomp := hα P hP
    have hπ : Fc.map ((NatTrans.mapHomologicalComplex
        (M.derived.ordinary.π n) (.up ℤ)).app P) ≫ γ.hom.app P =
        (NatTrans.mapHomologicalComplex (N.derived.ordinary.π n) (.up ℤ)).app
          (Fc.obj P) := by
      ext i
      exact he (P.X i)
    have hNnorm := N.normalization (Fc.obj P) n
    have hFnat := F.mapDerivedCategoryFactors_hom_naturality
      ((NatTrans.mapHomologicalComplex (M.derived.ordinary.π n) (.up ℤ)).app P)
    have hNnat := (N.unit n).naturality (F.mapDerivedCategoryFactors.hom.app P)
    dsimp only [Functor.id_map, Functor.comp_map] at hNnat
    dsimp only [z]
    rw [Category.assoc, ← hcomp]
    dsimp only [β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp, Category.assoc]
    dsimp only [Functor.comp_map]
    rw [← F.mapDerivedCategory.map_comp_assoc,
      ← F.mapDerivedCategory.map_comp_assoc, Category.assoc, M.normalization P n]
    erw [reassoc_of% hFnat]
    rw [← DerivedCategory.Q.map_comp, hπ]
    dsimp only [ε, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp]
    erw [← reassoc_of% hNnat]
    erw [hNnorm]
    rfl
  refine ⟨α, fun P ↦ ?_⟩
  simpa only [τ, σ, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp,
    Category.comp_id, Category.assoc] using congrArg (fun t ↦ t.app P) hτσ

private theorem ringRegularResolution
    {C : Type*} [Category* C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasSheafify J AddCommGrpCat.{v}]
    (R : Sheaf J CommRingCat.{v}) (ℓ : ℕ)
    (hm : ∀ n : ℕ, Mono (ℓ ^ (n + 1) • 𝟙
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{v} RingCat.{v})).obj R))))
    (K : CochainComplex (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat.{v} RingCat.{v})).obj R)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat.{v} RingCat.{v})).obj R)) ℤ) (p : P ⟶ K),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalPreadditive_kfi R
  obtain ⟨P, p, _, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  refine ⟨P, p, ?_, hq⟩
  intro n i
  let F := MonoidalCategory.tensorRight (P.X i)
  have : PreservesFiniteLimits F := (hf i).1
  have := hm n
  have h : Mono (F.map (ℓ ^ (n + 1) • 𝟙 (𝟙_ _))) := inferInstance
  have h' : Mono (ℓ ^ (n + 1) • 𝟙 (F.obj (𝟙_ _))) := by
    simpa only [F.map_nsmul, F.map_id] using h
  have he : (ℓ ^ (n + 1) • 𝟙 (P.X i)) ≫ (MonoidalCategory.leftUnitor (P.X i)).inv =
      (MonoidalCategory.leftUnitor (P.X i)).inv ≫
        (ℓ ^ (n + 1) • 𝟙 (F.obj (𝟙_ _))) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp]
    erw [Category.comp_id]
  exact mono_of_mono_fac he

private theorem transportRegularResolution
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] (ℓ : ℕ)
    (res : ∀ K : CochainComplex B ℤ,
      ∃ (P : CochainComplex B ℤ) (p : P ⟶ K),
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p)
    (K : CochainComplex A ℤ) :
    ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p := by
  obtain ⟨P, p, hm, hq⟩ := res ((e.functor.mapHomologicalComplex (.up ℤ)).obj K)
  let Pc := (e.inverse.mapHomologicalComplex (.up ℤ)).obj P
  let q : Pc ⟶ K := (e.inverse.mapHomologicalComplex (.up ℤ)).map p ≫
    (NatIso.mapHomologicalComplex e.unitIso (.up ℤ)).inv.app K
  have : QuasiIso p := hq
  refine ⟨Pc, q, ?_, inferInstance⟩
  intro n i
  have := hm n i
  have h := e.inverse.map_mono (ℓ ^ (n + 1) • 𝟙 (P.X i))
  change Mono (ℓ ^ (n + 1) • 𝟙 (e.inverse.obj (P.X i)))
  simpa only [e.inverse.map_nsmul, e.inverse.map_id] using h

private theorem flatAlgebraUnitMono
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsDomain A]
    (R : Sheaf J CommRingCat.{v})
    (α : SheafOfModules.scalarCyclicBase J A ⟶ R)
    (hflat : SheafOfModules.IsFlatOnSite (J := J)
      ((SheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{v} RingCat.{v})).map α)).obj
          (SheafOfModules.unit (SheafOfModules.scalarCyclicRing R))))
    (k : ℕ) (hk : (k : A) ≠ 0) :
    Mono (k • 𝟙 (SheafOfModules.unit (siteModuleRings R))) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U x y h
  have hx : k • (x - y) = 0 := by
    let H := SheafOfModules.forget (siteModuleRings R) ⋙
      PresheafOfModules.evaluation (siteModuleRings R).obj U
    change (H.map (k • 𝟙 (SheafOfModules.unit (siteModuleRings R)))) x =
      (H.map (k • 𝟙 (SheafOfModules.unit (siteModuleRings R)))) y at h
    rw [H.map_nsmul, H.map_id] at h
    have hxy : k • x = k • y := h
    simpa only [nsmul_sub, sub_eq_zero] using hxy
  apply sub_eq_zero.mp
  apply SheafOfModules.flat_scalar_kernel R α hflat (k : A) hk U (x - y)
  rw [SheafOfModules.scalar_cyclic_multiplication_apply]
  rw [SheafOfModules.scalar_cyclic_presheaf_map_apply]
  simp only [map_natCast]
  simpa only [← nsmul_eq_mul] using hx

private theorem smallCompletedUnitMono
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Mono (ℓ ^ (n + 1) • 𝟙 (SheafOfModules.unit
      (siteModuleRings
        (CategoryTheory.ConstantCompletion.completed J (ULift.{v} ℤ_[ℓ])
          (Ideal.span {(ℓ : ULift.{v} ℤ_[ℓ])}))))) := by
  let A := ULift.{v} ℤ_[ℓ]
  let : IsDomain A := ULift.ringEquiv.toMulEquiv.isDomain ℤ_[ℓ]
  let : CharZero A := ⟨fun a b h ↦ Nat.cast_injective (congrArg ULift.down h)⟩
  let I : Ideal A := Ideal.span {(ℓ : A)}
  let R := CategoryTheory.ConstantCompletion.completed J A I
  let α := CategoryTheory.ConstantCompletion.coefficientMap J A I
  let : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv ℤ_[ℓ] ULift.ringEquiv.symm
  have hflat := (CategoryTheory.ConstantCompletion.flat_and_quotients J A I).1
  let _ := SheafOfModules.monoidalCategory (SheafOfModules.scalarCyclicBase J A)
  have hflat' : SheafOfModules.IsFlatOnSite (J := J) (R := SheafOfModules.scalarCyclicBase J A)
      ((SheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{v} RingCat.{v})).map α)).obj
          (SheafOfModules.unit (SheafOfModules.scalarCyclicRing R))) := by
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (SheafOfModules.scalarCyclicBase J A)
        ((SheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{v} RingCat.{v})).map α)).obj
            (SheafOfModules.unit (SheafOfModules.scalarCyclicRing R)))).symm hflat
  exact flatAlgebraUnitMono J A R α hflat' (ℓ ^ (n + 1))
    (Nat.cast_ne_zero.mpr (pow_ne_zero (n + 1) (Fact.out : ℓ.Prime).ne_zero))

private theorem completedRegularResolution
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (K : CochainComplex (DiagonalCompleted ℓ W) ℤ) :
    ∃ (P : CochainComplex (DiagonalCompleted ℓ W) ℤ) (p : P ⟶ K),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p := by
  let J₀ := Scheme.ProEt.topology W
  let J := Scheme.proEtaleModelTopology W
  let A := ULift.{u + 1} ℤ_[ℓ]
  let I : Ideal A := Ideal.span {(ℓ : A)}
  let B₀ := Scheme.purTwistZlCompletion W ℓ
  let B := CategoryTheory.ConstantCompletion.completed J A I
  let e : W.ProEt ≌ Scheme.proEtaleSiteModel W := AsSmall.equiv.{u, u + 1, u + 1}
  let : e.functor.IsContinuous J₀ J := Scheme.proEtaleModelUp_isContinuous W
  let : e.inverse.IsContinuous J J₀ := inferInstanceAs
    ((AsSmall.down : Scheme.proEtaleSiteModel W ⥤ W.ProEt).IsContinuous
      (Scheme.proEtaleModelTopology W) (Scheme.ProEt.topology W))
  let f₀ := sheafCompose J₀ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let f := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let cB : f.obj B ≅
      (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} J J₀).obj (f₀.obj B₀) :=
    f.mapIso (DiagonalTrace.completedRingIso ℓ W)
  let EB := DiagonalTrace.moduleSiteEquivalence J₀ J e (f₀.obj B₀) (f.obj B) cB
  have : EB.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EB.inverse.Additive := Functor.additive_of_preserves_binary_products _
  exact transportRegularResolution EB ℓ
    (ringRegularResolution B ℓ (smallCompletedUnitMono J ℓ)) K

private theorem constantRegularResolution
    (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (K : CochainComplex (DiagonalMod ℓ W) ℤ) :
    ∃ (P : CochainComplex (DiagonalMod ℓ W) ℤ) (p : P ⟶ K),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p := by
  let A := ULift.{u + 1} ℤ_[ℓ]
  let : IsDomain A := ULift.ringEquiv.toMulEquiv.isDomain ℤ_[ℓ]
  let : CharZero A := ⟨fun a b h ↦ Nat.cast_injective (congrArg ULift.down h)⟩
  let S := constantSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)
  have hm (n : ℕ) : Mono (ℓ ^ (n + 1) • 𝟙 (𝟙_ (DiagonalMod ℓ W))) := by
    have hM : Mono (ℓ ^ (n + 1) • 𝟙 (𝟙_ (ModuleCat.{u + 1} A))) := by
      rw [ModuleCat.mono_iff_injective]
      change Function.Injective (fun x : A ↦ ℓ ^ (n + 1) • x)
      intro x y h
      apply mul_left_cancel₀ (show ((ℓ ^ (n + 1) : ℕ) : A) ≠ 0 from
        Nat.cast_ne_zero.mpr (pow_ne_zero (n + 1) (Fact.out : ℓ.Prime).ne_zero))
      exact (nsmul_eq_mul _ _).symm.trans (h.trans (nsmul_eq_mul _ _))
    have hS := S.map_mono (ℓ ^ (n + 1) • 𝟙 (𝟙_ (ModuleCat.{u + 1} A)))
    rw [S.map_nsmul, S.map_id] at hS
    let e := Functor.Monoidal.εIso S
    have he : (ℓ ^ (n + 1) • 𝟙 (𝟙_ (DiagonalMod ℓ W))) ≫ e.hom =
        e.hom ≫ (ℓ ^ (n + 1) • 𝟙 (S.obj (𝟙_ (ModuleCat.{u + 1} A)))) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  obtain ⟨P, p, hq, hf, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  refine ⟨P, p, ?_, hq⟩
  intro n i
  exact flat_multiplication_mono _ (hm n) (P.X i) (hf i)

/-- Simultaneous finite reduction commutes with exact completed scalar restriction,
including its quotient units, on all completed derived objects.

Source: Stacks 099I and 099M; blueprint diagonal tower limit proof, paragraph (3).
(blueprint: lem-sfb-diagonal-completed-reduction-restriction).
Proof: construct each ordinary reduction as the cokernel of multiplication by
ell^(n+1). Exact scalar restriction identifies these cokernels and their quotient
maps, naturally in the input and compatibly with the quotient transitions. Use
K-flat resolutions to derive the two simultaneous reduction functors. Restriction
preserves the regular resolving class, so uniqueness of pointwise left derived
functors gives the displayed natural isomorphisms. The ordinary cokernel square
identifies the localized quotient units with each other; descend the square through
the localization to obtain the stated equation on every derived object. -/
theorem diagonal_completed_reduction_restriction (ℓ : ℕ) [Fact ℓ.Prime]
    (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ W)] :
    let F := diagonalCompletedUnderlying ℓ W
    let E := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)).mapDerivedCategory
    let C := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ W)).obj (op n)).mapDerivedCategory
    ∃ (M : DiagonalCompletedReduction ℓ W)
      (N : DiagonalCompletedReductionData ℓ (DiagonalMod ℓ W)),
      ∀ n : ℕ, ∃ α : M.derived.T ⋙ C n ⋙ F ≅ F ⋙ N.derived.T ⋙ E n,
        ∀ P : DerivedCategory (DiagonalCompleted ℓ W),
          F.map ((M.unit n).app P) ≫ α.hom.app P = (N.unit n).app (F.obj P) := by
  dsimp only
  obtain ⟨M, hM⟩ := normalizedReductionExists ℓ (completedRegularResolution ℓ W)
  obtain ⟨N, hN⟩ := normalizedReductionExists ℓ (constantRegularResolution ℓ W)
  exact ⟨M, N, fun n ↦ reductionComparison ℓ (diagonalCompletedRestriction ℓ W)
    M N (completedRegularResolution ℓ W) hM hN n⟩

end AlgebraicGeometry.ProEtale
