/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.HomTensorDifferential
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatum
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus
import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Data.Nat.Prime.Infinite

/-! # Completeness under normalized integral coefficient transport

These coefficient equivalences and completeness comparisons are independent of
bounded constructibility and the stratified-perfect characterization.
Source: Stacks 099N; Bhatt--Scholze, Section 6.5
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CoefficientPresentation
variable (W : Scheme.{u})

/-- Lift the landed Ring-level coefficient comparison to commutative ring sheaves.
Its image under forgetting commutativity is the existing normalized comparison.
Source: Stacks 099N and Bhatt--Scholze 6.8.2(1)
(auxiliary; not a blueprint node).
Proof: a morphism between commutative rings is exactly a ring morphism. Thus the
forgetful functor on ring sheaves is fully faithful. Lift the existing comparison
and its inverse. Faithfulness gives their inverse identities and uniqueness. The
finite projection normalization is inherited from the landed comparison. -/
theorem purCoefficientIso_existsUnique :
    ∃! e : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E W,
      (adicLisseForget W).mapIso e = integralDetailedCoefficientComparison W l E := by
  let F := adicLisseForget W
  let hF := fullyFaithfulSheafCompose (ProEt.topology W)
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  refine ⟨hF.preimageIso (integralDetailedCoefficientComparison W l E), ?_, ?_⟩
  · apply Iso.ext
    exact hF.map_preimage _
  · intro e he
    apply F.mapIso_injective
    apply Iso.ext
    exact (congrArg Iso.hom he).trans (hF.map_preimage _).symm

/-- The CommRing lift of integralDetailedCoefficientComparison, with no new choice
of normalization. Source: Stacks 099N
(auxiliary; not a blueprint node). -/
def purCoefficientIso := (purCoefficientIso_existsUnique l E W).exists.choose

end CoefficientPresentation

section RestrictionEquivalence
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{u + 1}}

end RestrictionEquivalence

end WeilConjectures
