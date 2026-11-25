/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteConstructibilityOuterTransfer
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsSerre
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! Weak-Serre closure for fixed-stratum finite local models. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

open FiniteDiscreteOrdinary

private theorem finite_iff_fixedModels
    (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B)) :
    IsFiniteLocallyConstant B F ↔
      Scheme.ProFiniteModels.fixedModels (Scheme.ProEt.topology T) B F := by
  constructor
  · intro h V
    have ht := (Scheme.CoefficientSerre.fixedFiniteSieve_iff B F).mpr h
    let a := terminal.from V
    have hv := (Scheme.ProEt.topology T).pullback_stable a ht
    refine ⟨_, hv, ?_⟩
    rintro W f ⟨M, hM, ⟨e⟩⟩
    have := hM
    exact ⟨M, Module.Finite.of_finite, ⟨e ≪≫
      ((Scheme.ProEt.topology T).overPullbackConstantSheafIso
        (ModuleCat.{u + 1} B) W).app M⟩⟩
  · intro h
    apply (Scheme.CoefficientSerre.fixedFiniteSieve_iff B F).mp
    obtain ⟨S, hS, hs⟩ := h (⊤_ T.ProEt)
    apply (Scheme.ProEt.topology T).superset_covering _ hS
    intro W f hf
    obtain ⟨M, hM, ⟨e⟩⟩ := hs W f hf
    have := hM
    exact ⟨M, Module.finite_of_finite B, ⟨e ≪≫
      (((Scheme.ProEt.topology T).overPullbackConstantSheafIso
        (ModuleCat.{u + 1} B) W).app M).symm⟩⟩

private theorem localCondition_iff_fp
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) (F : Ordinary A T) :
    ordinaryFiniteLocalCondition A T F ↔
      Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule F := by
  exact (Scheme.finiteLocal_iff T A F).symm.trans
    ((finite_iff_fixedModels T (ULift.{u + 1} A) _).trans
      (Scheme.ProFiniteModels.intrinsic_fixedModels T A F).symm)

private theorem finite_local_triangle
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    (Δ : CategoryTheory.Pretriangulated.Triangle (DerivedCategory (Internal A X)))
    (hΔ : Δ ∈ distTriang _)
    (h₁ : scalarFiniteLocalModelsOnStratum (coefficient A) X S i Δ.obj₁)
    (h₃ : scalarFiniteLocalModelsOnStratum (coefficient A) X S i Δ.obj₃) :
    scalarFiniteLocalModelsOnStratum (coefficient A) X S i Δ.obj₂ := by
  let T := S.domain i
  let e := (encoding_exists A T).some
  let H := CondensedRing.upperStar (coefficient A) (S.immersion i) ⋙ e.ordinary.functor
  let Q : ObjectProperty (Ordinary A T) :=
    Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun j hj ↦ Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule_of_iso j hj⟩
  obtain ⟨hkc, hext⟩ := Scheme.proEtale_fp_localModels_serre T A
  have : Q.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact Q.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).1⟩
  have : Q.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact Q.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).2⟩
  have : Q.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ hext _ hS h1 h3⟩
  let P : ObjectProperty (Internal A X) := Q.inverseImage H
  have : P.IsClosedUnderIsomorphisms := inferInstance
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact Q.prop_of_iso
      ((PreservesKernel.iso H f).symm ≪≫ H.mapIso
        ((kernelIsKernel f).conePointUniqueUpToIso hk))
      (Q.prop_kernel (H.map f) hFG.1 hFG.2)⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact Q.prop_of_iso
      ((PreservesCokernel.iso H f).symm ≪≫ H.mapIso
        ((cokernelIsCokernel f).coconePointUniqueUpToIso hk))
      (Q.prop_cokernel (H.map f) hFG.1 hFG.2)⟩
  have : P.IsClosedUnderExtensions := inferInstance
  have hm (M : Internal A X) :
      HasFiniteConstantLocalModel (coefficient A) T
        ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) ↔ P M :=
    (localCondition_iff A T e _).trans (localCondition_iff_fp A T _)
  have h₁' : DerivedCategory.homologyProperty P Δ.obj₁ := fun q ↦ (hm _).mp (h₁ q)
  have h₃' : DerivedCategory.homologyProperty P Δ.obj₃ := fun q ↦ (hm _).mp (h₃ q)
  have h₂ := (DerivedCategory.homologyProperty P).ext_of_isTriangulatedClosed₂
    Δ hΔ h₁' h₃'
  exact fun q ↦ (hm _).mpr (h₂ q)

/-- Fixed-stratum finite models are closed under distinguished triangles over a positive
finite quotient. Source: blueprint latest, integral-finite-levels, first paragraph.
(blueprint: lem-pe-finite-constructibility-middle-closure).

Proof: finite quotient coefficients are a finite Noetherian discrete ring. Normalized
encoding identifies finite constant models with finite locally constant modules.
Their kernels, cokernels and extensions are again finite locally constant. Exact
inverse image along the specified immersion pulls this weak Serre class back to the
ambient scheme. The five-term homology sequence proves the assertion in each degree. -/
theorem finite_constructibility_local_triangle
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) (S : Scheme.Stratification X) (i : Fin S.n)
    (Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n))))
    (hΔ : Δ ∈ distTriang _)
    (h₁ : scalarFiniteLocalModelsOnStratum
      (DerivedNakayama.quotientRing l E (n + 1)) X S i Δ.obj₁)
    (h₃ : scalarFiniteLocalModelsOnStratum
      (DerivedNakayama.quotientRing l E (n + 1)) X S i Δ.obj₃) :
    scalarFiniteLocalModelsOnStratum
      (DerivedNakayama.quotientRing l E (n + 1)) X S i Δ.obj₂  := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let := DerivedNakayama.quotientDiscrete l E (n + 1)
  exact finite_local_triangle (Padic.coefficientExtensionRing l E (n + 1))
    X S i Δ hΔ h₁ h₃

end AlgebraicGeometry.ProEtale
