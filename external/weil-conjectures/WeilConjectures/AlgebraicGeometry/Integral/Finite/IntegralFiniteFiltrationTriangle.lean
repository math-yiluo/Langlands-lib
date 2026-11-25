/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteResidueNormalization
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
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteQuotientTriangle

/-! # Native quotient-linear uniformizer filtration triangles
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

attribute [local instance] DerivedNakayama.pullbackFiniteLimits
  DerivedNakayama.pullbackFiniteColimits

private def extensionCongr
    {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    {φ ψ : R ⟶ S} [IsMonHom φ] [IsMonHom ψ] (h : φ = ψ) :
    (Mod.extendScalars φ).leftDerivedFunctor ≅
      (Mod.extendScalars ψ).leftDerivedFunctor := by
  subst ψ
  exact Iso.refl _

/-- The consecutive coefficient filtration is a triangle over the larger finite quotient. -/
theorem integral_finite_filtration_triangle
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ) :
    ∃ Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X (n + 1)))),
      Δ ∈ distTriang _ ∧
      Nonempty (Δ.obj₁ ≅
        (Mod.comap (integralResidueTransition l E X (n + 1))).mapDerivedCategory.obj
          ((AdicCompletion.derivedReduction l E X 0).obj K)) ∧
      Nonempty (Δ.obj₂ ≅ (AdicCompletion.derivedReduction l E X (n + 1)).obj K) ∧
      Nonempty (Δ.obj₃ ≅ (Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj
        ((AdicCompletion.derivedReduction l E X n).obj K)) := by
  classical
  let F := DerivedNakayama.pullback l E X
  obtain ⟨i, q, _, _, hseq⟩ := DerivedNakayama.PowerQuotients.sequences
    (DerivedNakayama.uniformizerEnd l E) (DerivedNakayama.quotientModule l E)
    (DerivedNakayama.reductionHom l E) (DerivedNakayama.reduction_zero l E)
    (DerivedNakayama.pointResolution l E)
  obtain ⟨hz, hshort⟩ := hseq 1 (n + 1)
  let Q := AdicCompletion.quotient l E X (n + 1)
  let t := integralResidueTransition l E X (n + 1)
  let s := AdicCompletion.transition l E X n
  have ht : Q ≫ t = AdicCompletion.quotient l E X 0 :=
    integralResidueTransition_quotient l E X (n + 1)
  have hs : Q ≫ s = AdicCompletion.quotient l E X n :=
    AdicCompletion.quotient_transition l E X n
  let eB (k : ℕ) := (Functor.mapModComapIso (upperStarFromPoint X)
    (DerivedNakayama.reductionRing l E (k + 1))).app
      (Mod.regular (DerivedNakayama.quotientRing l E (k + 1)))
  let e₁ := eB 0 ≪≫ (Mod.comapCongr ht.symm).app
    (Mod.regular (AdicCompletion.finiteRing l E X 0))
  let e₂ := eB (n + 1)
  let e₃ := eB n ≪≫ (Mod.comapCongr hs.symm).app
    (Mod.regular (AdicCompletion.finiteRing l E X n))
  let f := e₁.inv ≫ F.map (i 1 (n + 1)) ≫ e₂.hom
  let g := e₂.inv ≫ F.map (q 1 (n + 1)) ≫ e₃.hom
  have hfg : f ≫ g = 0 := by
    simp only [f, g, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F.map_comp_assoc, hz, F.map_zero, zero_comp, comp_zero]
  have hS : (ShortComplex.mk f g hfg).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e₁ e₂ e₃ (by simp [f]) (by simp [g]))
      (hshort.map_of_exact F)
  have hQ : Epi Q := by
    have h := (DerivedNakayama.pointResolution l E (n + 2)).map_of_exact F
    have he : Epi (F.map (DerivedNakayama.reductionHom l E (n + 2))) := h.epi_g
    have : (Mod.forget (AdicCompletion.ring l E X) :
        AdicCompletion.Modules l E X ⥤
          Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}).PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
    exact (Mod.forget (AdicCompletion.ring l E X)).map_epi
      (F.map (DerivedNakayama.reductionHom l E (n + 2)))
  obtain ⟨Δ, hΔ, ⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := quotientScalarTriangle Q t s
    (fun Z ↦ (tensorRight Z).map_epi Q) f g hfg hS K
  have et : (Mod.extendScalars (Q ≫ t)).leftDerivedFunctor.obj K ≅
      (AdicCompletion.derivedReduction l E X 0).obj K := (extensionCongr ht).app K
  have es : (Mod.extendScalars (Q ≫ s)).leftDerivedFunctor.obj K ≅
      (AdicCompletion.derivedReduction l E X n).obj K := (extensionCongr hs).app K
  exact ⟨Δ, hΔ, ⟨a ≪≫ (Mod.comap t).mapDerivedCategory.mapIso et⟩, ⟨b⟩,
    ⟨c ≪≫ (Mod.comap s).mapDerivedCategory.mapIso es⟩⟩

end AlgebraicGeometry.ProEtale
