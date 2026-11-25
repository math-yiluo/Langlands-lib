/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
/-! # Isomorphism invariance of coefficient constructibility
Source: Stacks Tag 09AJ, constructibility by finite local models.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- A module isomorphism transports the same affine-local strata and finite models.
Source: Stacks Tag 09AJ (auxiliary; not a blueprint node).
Proof: on each affine open retain its stratification. Restrict the isomorphism to
each stratum and every slice, using functoriality of scalar restriction and inverse
image. Compose its inverse with the given constant trivialization. Finite type and
finite presentation agree over the Noetherian coefficient ring, so the finite-model
isomorphism-invariance theorem gives exactly the recorded presentation predicate. -/
theorem coefficientProEtale_constructible_of_iso (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    {F G : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)} (e : F ≅ G)
    (h : Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F) :
    Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A G := by
  intro U hU
  obtain ⟨S, hc, hs⟩ := h U hU
  refine ⟨S, hc, ?_⟩
  intro a V
  have hfinite : IsCoefficientModelLocallyConstantFinite _ A
      ((Scheme.coefficientProEtaleFixedModulePullback (S.immersion a ≫ U.ι) A).obj
        ((coefficientModelFixedScalars _ A).obj F)) := by
    intro W
    obtain ⟨T, hT, ht⟩ := hs a W
    refine ⟨T, hT, ?_⟩
    intro Z f hf
    obtain ⟨M, hM, e⟩ := ht Z f hf
    have := hM
    exact ⟨M, inferInstance, e⟩
  have hg := coefficientProEtale_finite_iso A
    ((Scheme.coefficientProEtaleFixedModulePullback (S.immersion a ≫ U.ι) A).mapIso
      ((coefficientModelFixedScalars _ A).mapIso e)) hfinite
  obtain ⟨T, hT, ht⟩ := hg V
  refine ⟨T, hT, ?_⟩
  intro W f hf
  obtain ⟨M, hM, e⟩ := ht W f hf
  have := hM
  exact ⟨M, Module.finitePresentation_of_finite A M, e⟩

end AlgebraicGeometry.ProEtale
