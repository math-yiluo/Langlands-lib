/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper

Modified by Worker 50 (2026): specialize the localization argument of Imperial FLT,
commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/IntegralClosure.lean:207-297 to number fields in independent
universes and prove bijectivity of the Library's actual integralTensorTransport.
Use Mathlib's IsBaseChange.equiv for the fraction-field tensor equivalence and
only its existing moduleTensorEquiv and moduleLid interfaces. No external module
or leftModuleTensorEquiv is imported. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonStatement
import Mathlib.RingTheory.Localization.BaseChange

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

private def integralFieldTensorEquiv : K ⊗[𝓞 K] 𝓞 L ≃ₗ[K] L := by
  haveI := IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K
    (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap).equiv

private theorem integralFieldTensorEquiv_one_tmul (b : 𝓞 L) :
    integralFieldTensorEquiv K L (1 ⊗ₜ[𝓞 K] b) = algebraMap (𝓞 L) L b := by
  simp [integralFieldTensorEquiv, IsBaseChange.equiv_tmul]

variable {K}

private def integralTransportEquiv (p : HeightOneSpectrum (𝓞 K)) :
    𝓞 L ⊗[𝓞 K] p.adicCompletion K ≃ₗ[𝓞 K] p.adicCompletion K ⊗[K] L :=
  let e₁ := TensorProduct.congr (LinearEquiv.refl (𝓞 K) (𝓞 L))
    ((IsLocalization.moduleLid (nonZeroDivisors (𝓞 K)) K
      (p.adicCompletion K)).restrictScalars (𝓞 K)).symm
  let e₂ := (TensorProduct.assoc (𝓞 K) (𝓞 L) K (p.adicCompletion K)).symm
  let e₃ := TensorProduct.congr
    ((TensorProduct.comm (𝓞 K) (𝓞 L) K).trans
      ((integralFieldTensorEquiv K L).restrictScalars (𝓞 K)))
    (LinearEquiv.refl (𝓞 K) (p.adicCompletion K))
  let e₄ := ((IsLocalization.moduleTensorEquiv (nonZeroDivisors (𝓞 K)) K L
    (p.adicCompletion K)).restrictScalars (𝓞 K)).symm
  let e₅ := (TensorProduct.comm K L (p.adicCompletion K)).restrictScalars (𝓞 K)
  e₁.trans e₂ |>.trans e₃ |>.trans e₄ |>.trans e₅

private theorem integralTransportEquiv_tmul (p : HeightOneSpectrum (𝓞 K))
    (b : 𝓞 L) (x : p.adicCompletion K) :
    integralTransportEquiv L p (b ⊗ₜ[𝓞 K] x) =
      x ⊗ₜ[K] algebraMap (𝓞 L) L b := by
  simp [integralTransportEquiv, IsLocalization.moduleLid,
    IsLocalization.moduleTensorEquiv, TensorProduct.equivOfCompatibleSMul,
    integralFieldTensorEquiv_one_tmul]

/-- The canonical coefficient and tensor-order transport is bijective. -/
theorem integralTensorTransportBijective : IntegralTensorTransportBijective.{u, v} := by
  intro K L _ _ _ _ _ p
  have h : (integralTensorTransport L p : _ → _) = integralTransportEquiv L p := by
    funext z
    induction z with
    | tmul b x => rw [integralTensorTransport_tmul, integralTransportEquiv_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  rw [h]
  exact (integralTransportEquiv L p).bijective

end Langlands.Global.AdelicFunctoriality
