/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
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
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # The native uniformizer coefficient cone -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The actual positive uniformizer quotient as an integral module. -/
def nativeCoefficientLevel (n : ℕ) :=
  (Mod.comap (coefficientMap (twistReduction l E n) X)).obj
    (Mod.regular (condensedRingObj (twistFiniteRing l E n) X))

/-- Linear quotient transition, with the specified reduction as its underlying map. -/
def nativeCoefficientTransition (n : ℕ) :
    nativeCoefficientLevel l E X (n + 1) ⟶ nativeCoefficientLevel l E X n :=
  Mod.homMk (coefficientMap (twistFiniteReduction l E n) X) (by
    change (_ ▷ _) ≫ μ[_] ≫ coefficientMap (twistFiniteReduction l E n) X =
      _ ◁ coefficientMap (twistFiniteReduction l E n) X ≫ (_ ▷ _) ≫ μ[_]
    rw [IsMonHom.mul_hom]
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp, twistReduction_comp])

/-- The actual positive uniformizer quotient diagram. -/
def nativeCoefficientSystem := Functor.ofOpSequence (nativeCoefficientTransition l E X)

private abbrev continuousAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousCoefficientRingSheaf X A)

private def continuousMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : continuousAb X A ⟶ continuousAb X B :=
  ⟨{ app := fun _ ↦ AddCommGrpCat.ofHom
      (ULift.ringEquiv.symm.toAddEquiv.toAddMonoidHom.comp
        ((f.compLeftContinuous _ hf).toAddMonoidHom.comp
          ULift.ringEquiv.toAddEquiv.toAddMonoidHom))
     naturality := fun _ _ _ ↦ rfl }⟩

private theorem realization_natural {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    (upperStarFromPoint X).map (twistContinuousMap f hf) ≫
        ContinuousRingUniverse.comparison X B =
      ContinuousRingUniverse.comparison X A ≫ continuousMap X f hf := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [ContinuousRingUniverse.comparison]
  change _ ≫ adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) =
    adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext S x
  rfl

private abbrev continuousFinite (n : ℕ) :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  continuousAb X (Padic.coefficientExtensionRing l E (n + 1))

private def continuousTransition (n : ℕ) :
    continuousFinite l E X (n + 1) ⟶ continuousFinite l E X n :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 2)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 2)) := ⟨rfl⟩
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  continuousMap X (Padic.coefficientExtensionTransition l E (n + 1))
    continuous_of_discreteTopology

private def continuousSequence := Functor.ofOpSequence (continuousTransition l E X)

private def continuousProjection (n : ℕ) :
    letI := spectralNorm.normedField ℚ_[l] E
    continuousAb X (Padic.coefficientExtensionIntegers l E) ⟶ continuousFinite l E X n :=
  letI := spectralNorm.normedField ℚ_[l] E
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  continuousMap X (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (twistReduction_continuous l E n)

private def continuousCone : Cone (continuousSequence l E X) := by
  let := spectralNorm.normedField ℚ_[l] E
  refine ⟨continuousAb X (Padic.coefficientExtensionIntegers l E),
    NatTrans.ofOpSequence (continuousProjection l E X) ?_⟩
  intro n
  dsimp only [continuousSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  ext U f
  rfl

end AlgebraicGeometry.ProEtale
