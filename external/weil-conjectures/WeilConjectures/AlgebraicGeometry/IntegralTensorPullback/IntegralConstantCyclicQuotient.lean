/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import Mathlib.CategoryTheory.Adjunction.Limits

set_option linter.privateModule false

/-! # The two coefficient units present the same positive cyclic quotient
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w a b c d
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem adjointSquare
    {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {P Q : A} {R S : B} (a : P ⟶ Q) (b : R ⟶ S)
    (σ : P ⟶ G.obj R) (τ : Q ⟶ G.obj S)
    (h : a ≫ τ = σ ≫ G.map b) :
    F.map a ≫ (adj.homEquiv _ _).symm τ = (adj.homEquiv _ _).symm σ ≫ b := by
  exact adj.homEquiv_naturality_right_square a τ σ b h

section ScalarActions
variable {C : Type v} [Category.{w} C] [Abelian C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

end ScalarActions

private def mapRegularIso
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] :
    (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
  Mod.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp])

private def scalarQuotient (n : ℕ) :
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x.down)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
