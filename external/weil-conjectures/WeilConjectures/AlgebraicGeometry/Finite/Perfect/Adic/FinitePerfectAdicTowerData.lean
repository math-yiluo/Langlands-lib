/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
public import WeilConjectures.RingTheory.RlimPerfectComplete
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
public import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule
public import WeilConjectures.RingTheory.NilpotentTorsionDerivedLimitComplete
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.DerivedCompleteProductsTriangles
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.RingTheory.Nilpotent.Basic
public import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstruction
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstructionModels
public import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import WeilConjectures.RingTheory.PseudoCoherentNilpotentInvariance
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.RingTheory.NilpotentProjectiveComplexLift
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.AlgebraicGeometry.ComplexLiftClassProjective
public import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.NilpotentDerivedUpperBoundSupplement
public import WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
public import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.RingTheory.NilpotentProjectiveModuleLift
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Idempotents
public import WeilConjectures.RingTheory.NakayamaNilpotent
public import WeilConjectures.RingTheory.FiniteProjectiveFreeModIdeal
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.Algebra.Homology.ProperBaseChange.SurjectiveModuleComplexTowerLimitSupplement
public import WeilConjectures.RingTheory.NilpotentMarkedFreeComplexLift
public import WeilConjectures.RingTheory.UnmarkedFiniteFreeLift
public import WeilConjectures.RingTheory.StablyFreeComplexLift
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal
public import WeilConjectures.RingTheory.MarkedFiniteFreeLiftCompatibility
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
public import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.AlgebraicGeometry.ComplexLiftConeProperties
public import WeilConjectures.AlgebraicGeometry.ComplexLiftStrictMap
public import WeilConjectures.AlgebraicGeometry.ComplexLiftConeCokernel
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.AcyclicLift
public import WeilConjectures.AlgebraicGeometry.ProjectiveClassReducedSplitting
public import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.PseudoCoherentNormalizedAlgebraTowerSupplement
public import WeilConjectures.RingTheory.PseudoCoherentMaximalFibrePerfect
public import WeilConjectures.Algebra.Homology.FreeComplexResidueTensorExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.Algebra.Homology.FreeComplexResidueDegreeCancellation
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import WeilConjectures.Algebra.Homology.LocalizedExactPairContraction
public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.Algebra.Homology.PrincipalContractionSpreading
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-! # Data of the algebraic tower underlying local finite perfect models

Source: Stacks Project, Tag 09C6, the construction of the algebraic normalized tower;
Tags 09B1 and 09BV for its compatible local comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The small localization furnished by the Grothendieck universal construction.
Source: Stacks Tag 05RU. -/
abbrev finitePerfectAdicAlgebraDerived (R : Type t) [CommRing R] :
    HasDerivedCategory.{t} (ModuleCat.{t} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Exact constant realization, including the recorded coefficient-universe lift.
Source: Stacks Tags 093J and 03CY. -/
def finitePerfectAdicConstant (X : Scheme.{t}) (A : Type t) [CommRing A] :
    ModuleCat.{t} A ⥤ SheafOfModules.{t + 1} (adicModuleRing X A) :=
  ModuleCat.uliftFunctor.{t + 1, t} A ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom ⋙
    koszulConstantFunctor X A

theorem finitePerfectAdicConstant_exact (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (finitePerfectAdicConstant X A).Additive ∧
      PreservesFiniteLimits (finitePerfectAdicConstant X A) ∧
      PreservesFiniteColimits (finitePerfectAdicConstant X A) := by
  have h := commutativeSiteConstantModuleFunctor_exact
    (ProEt.topology X) (ULift.{t + 1} A)
  have h' : (koszulConstantFunctor X A).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor X A) ∧
      PreservesFiniteColimits (koszulConstantFunctor X A) := h
  have := h'.1
  have := h'.2.1
  have := h'.2.2
  have he : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  unfold finitePerfectAdicConstant
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The exact derived constant functor on the chosen small algebraic localization.
Source: Stacks Tag 05RU. -/
def finitePerfectAdicDerivedConstant (X : Scheme.{t}) (A : Type t) [CommRing A] :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  (finitePerfectAdicConstant X A).mapDerivedCategory

/-- A normalized algebraic quotient system, including its actual adjunctions.
Source: Stacks Tags 09AW and 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
structure FinitePerfectAdicAlgebraTower {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) where
  level : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  transition : ∀ n : ℕ, level (n + 1) ⟶
    (DerivedCategory.adicStepRestriction d.ideal n).obj (level n)
  extension : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
    DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  adjunction : ∀ n : ℕ, extension n ⊣ DerivedCategory.adicLevelRestriction d.ideal n
  stepExtension : ∀ n : ℕ,
    DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  stepAdjunction : ∀ n : ℕ, stepExtension n ⊣ DerivedCategory.adicStepRestriction d.ideal n
  normalized : ∀ n : ℕ, IsIso
    (((stepAdjunction n).homEquiv (level (n + 1)) (level n)).symm (transition n))
  residuePerfect : DerivedCategory.IsPerfect (level 0)

/-- Completed constant realization, followed by exact slice restriction.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicLocalRealization (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt) :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
  finitePerfectAdicDerivedConstant X A ⋙
    completedAdicDerivedChange X (completedAdicScalar X d) ⋙
      ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) U

/-- The levelwise derived diagram of the specified strict tower, restricted to a slice.
Source: Stacks Tags 0940 and 0941.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicRestrictedTower (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d)) :
    ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
  (DerivedCategory.Q.objPreimage Z).asFunctor ⋙ DerivedCategory.Q ⋙
    ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) U

/-- A compatible trivialization of the entire diagram, rather than unrelated level isomorphisms.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
structure FinitePerfectAdicLocalTower (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d)) extends FinitePerfectAdicAlgebraTower d where
  comparison : Nonempty (finitePerfectAdicRestrictedTower X d U Z ≅
    Functor.ofOpSequence (X := fun n ↦
      (DerivedCategory.adicLevelRestriction d.ideal n).obj (level n))
      (DerivedCategory.adicTowerTransition d.ideal level transition) ⋙
      finitePerfectAdicLocalRealization X d U)

/-- The diagram realized by a specified algebraic quotient tower.
Source: Stacks Tag 09C6 (blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicModelDiagram (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt) (T : FinitePerfectAdicAlgebraTower d) :=
  Functor.ofOpSequence (X := fun n ↦
    (DerivedCategory.adicLevelRestriction d.ideal n).obj (T.level n))
    (DerivedCategory.adicTowerTransition d.ideal T.level T.transition) ⋙
    finitePerfectAdicLocalRealization X d U

/-- Regard a pro-etale object of an etale chart as an object over the original base.
Source: Stacks Tags 094T and 0951
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicChartObject {X : Scheme.{t}} (V : X.Etale) (U : V.left.ProEt) :
    X.ProEt := ProEt.mk (U.hom ≫ V.hom)

end AlgebraicGeometry.Scheme
