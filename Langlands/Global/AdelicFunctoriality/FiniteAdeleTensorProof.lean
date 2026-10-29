/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper

Modified by Workers 98 and 100 (2026): adapt the global bijectivity argument of Imperial FLT,
commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:129-252 to the Library's
canonical tensor map, with independent field universes and private localization
and restricted-product helpers. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorStatement
import Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonProof
import Langlands.LinearAlgebra.RestrictedProduct.TensorEquiv
import Langlands.LinearAlgebra.RestrictedProduct.Equiv
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct FiniteExtension RestrictedProduct

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

private def globalIntegralFieldEquiv : K ⊗[𝓞 K] 𝓞 L ≃ₗ[K] L := by
  haveI := IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K
    (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap).equiv

private theorem globalIntegralFieldEquiv_one_tmul (b : 𝓞 L) :
    globalIntegralFieldEquiv K L (1 ⊗ₜ[𝓞 K] b) = algebraMap (𝓞 L) L b := by
  simp [globalIntegralFieldEquiv, IsBaseChange.equiv_tmul]

private def globalIntegralTransport :
    𝓞 L ⊗[𝓞 K] FiniteAdeleRing (𝓞 K) K ≃ₗ[𝓞 K]
      FiniteAdeleRing (𝓞 K) K ⊗[K] L :=
  let e₁ := TensorProduct.congr (LinearEquiv.refl (𝓞 K) (𝓞 L))
    ((IsLocalization.moduleLid (nonZeroDivisors (𝓞 K)) K
      (FiniteAdeleRing (𝓞 K) K)).restrictScalars (𝓞 K)).symm
  let e₂ := (TensorProduct.assoc (𝓞 K) (𝓞 L) K (FiniteAdeleRing (𝓞 K) K)).symm
  let e₃ := TensorProduct.congr
    ((TensorProduct.comm (𝓞 K) (𝓞 L) K).trans
      ((globalIntegralFieldEquiv K L).restrictScalars (𝓞 K)))
    (LinearEquiv.refl (𝓞 K) (FiniteAdeleRing (𝓞 K) K))
  let e₄ := ((IsLocalization.moduleTensorEquiv (nonZeroDivisors (𝓞 K)) K L
    (FiniteAdeleRing (𝓞 K) K)).restrictScalars (𝓞 K)).symm
  let e₅ := (TensorProduct.comm K L (FiniteAdeleRing (𝓞 K) K)).restrictScalars (𝓞 K)
  e₁.trans e₂ |>.trans e₃ |>.trans e₄ |>.trans e₅

private theorem globalIntegralTransport_tmul (b : 𝓞 L) (x : FiniteAdeleRing (𝓞 K) K) :
    globalIntegralTransport K L (b ⊗ₜ[𝓞 K] x) = x ⊗ₜ[K] algebraMap (𝓞 L) L b := by
  simp [globalIntegralTransport, IsLocalization.moduleLid,
    IsLocalization.moduleTensorEquiv, TensorProduct.equivOfCompatibleSMul,
    globalIntegralFieldEquiv_one_tmul]

private def integralSubmodule (p : HeightOneSpectrum (𝓞 K)) :
    Submodule (𝓞 K) (p.adicCompletion K) where
  carrier := p.adicCompletionIntegers K
  zero_mem' := (p.adicCompletionIntegers K).zero_mem
  add_mem' := fun hx hy => (p.adicCompletionIntegers K).add_mem _ _ hx hy
  smul_mem' a x hx := by
    rw [Algebra.smul_def]
    exact mul_mem (coe_mem_adicCompletionIntegers p a) hx

private def adeleModuleEquiv : FiniteAdeleRing (𝓞 K) K ≃ₗ[𝓞 K]
    Πʳ p, [p.adicCompletion K, integralSubmodule K p] where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply RestrictedProduct.ext
    intro p
    exact (Algebra.smul_def a (x p)).symm

private def adeleTensorRestrictedEquiv :
    𝓞 L ⊗[𝓞 K] FiniteAdeleRing (𝓞 K) K ≃ₗ[𝓞 K]
      Πʳ p, [𝓞 L ⊗[𝓞 K] p.adicCompletion K,
        RestrictedProduct.rangeLTensor (𝓞 K) (𝓞 L) (adicCompletion K) (integralSubmodule K) p] := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 L) :=
    Module.finitePresentation_of_finite (𝓞 K) (𝓞 L)
  haveI : FaithfulSMul (𝓞 K) (𝓞 L) :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 L) K L
  exact (TensorProduct.congr (LinearEquiv.refl (𝓞 K) (𝓞 L)) (adeleModuleEquiv K)).trans
    (RestrictedProduct.lTensorEquiv (𝓞 K) (𝓞 L) (adicCompletion K) .cofinite (integralSubmodule K))

omit [NumberField L] in
private theorem tensorRange_eq_integralTensorInclusion (p : HeightOneSpectrum (𝓞 K)) :
    (RestrictedProduct.rangeLTensor (𝓞 K) (𝓞 L) (adicCompletion K)
      (integralSubmodule K) p : Set (𝓞 L ⊗[𝓞 K] p.adicCompletion K)) =
      Set.range (integralTensorInclusion L p) := by
  rfl

private theorem adeleTensorRestrictedEquiv_tmul (b : 𝓞 L)
    (x : FiniteAdeleRing (𝓞 K) K) (p : HeightOneSpectrum (𝓞 K)) :
    adeleTensorRestrictedEquiv K L (b ⊗ₜ[𝓞 K] x) p = b ⊗ₜ[𝓞 K] x p := by
  simp only [adeleTensorRestrictedEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, RestrictedProduct.lTensorEquiv_tmul]
  rfl

private def globalLocalFiberEquiv (p : HeightOneSpectrum (𝓞 K)) :
    (𝓞 L ⊗[𝓞 K] p.adicCompletion K) ≃
      ((q : {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p}) →
        q.1.adicCompletion L) :=
  (Equiv.ofBijective (integralTensorComparison L p)
    (integralLocalTensorComparison K L p).1).trans
    { toFun := fun f q => f ((finitePlacesAboveEquiv L p).symm q)
      invFun := fun f q => f (finitePlacesAboveEquiv L p q)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem globalLocalFiberEquiv_apply (p : HeightOneSpectrum (𝓞 K))
    (z : 𝓞 L ⊗[𝓞 K] p.adicCompletion K)
    (q : {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p}) :
    globalLocalFiberEquiv K L p z q =
      integralTensorComparison L p z ((finitePlacesAboveEquiv L p).symm q) := by
  rfl

private theorem globalLocalFiberEquiv_bijOn (p : HeightOneSpectrum (𝓞 K)) :
    Set.BijOn (globalLocalFiberEquiv K L p) (Set.range (integralTensorInclusion L p))
      (Set.pi Set.univ
        (fun q : {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p} =>
          (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)))) := by
  have h := (integralLocalTensorComparison K L p).2.2
  refine ⟨?_, (globalLocalFiberEquiv K L p).injective.injOn, ?_⟩
  · intro z hz q _
    exact h.mapsTo hz ((finitePlacesAboveEquiv L p).symm q) trivial
  · intro y hy
    let y' : (q : FinitePlacesAbove L p) → q.1.adicCompletion L :=
      fun q => y (finitePlacesAboveEquiv L p q)
    have hy' : y' ∈ Set.pi Set.univ
        (fun q : FinitePlacesAbove L p =>
          (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) := by
      intro q _
      exact hy (finitePlacesAboveEquiv L p q) trivial
    obtain ⟨z, hz, he⟩ := h.surjOn hy'
    refine ⟨z, hz, ?_⟩
    funext q
    change integralTensorComparison L p z ((finitePlacesAboveEquiv L p).symm q) = y q
    rw [he]
    rfl

private def globalLocalRestrictedEquiv :
    (Πʳ p : HeightOneSpectrum (𝓞 K),
      [𝓞 L ⊗[𝓞 K] p.adicCompletion K,
        RestrictedProduct.rangeLTensor (𝓞 K) (𝓞 L) (adicCompletion K)
          (integralSubmodule K) p]) ≃
    (Πʳ p : HeightOneSpectrum (𝓞 K),
      [(q : {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p}) → q.1.adicCompletion L,
        Set.pi Set.univ (fun q =>
          (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)))]) :=
  Equiv.restrictedProductCongrRight (globalLocalFiberEquiv K L)
    (Filter.Eventually.of_forall fun p => by
      rw [tensorRange_eq_integralTensorInclusion]
      exact globalLocalFiberEquiv_bijOn K L p)

private def globalFlattenEquiv :
    (Πʳ p : HeightOneSpectrum (𝓞 K),
      [(q : {q : HeightOneSpectrum (𝓞 L) // q.under (𝓞 K) = p}) → q.1.adicCompletion L,
        Set.pi Set.univ (fun q =>
          (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L)))]) ≃
      FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.flattenEquiv'
    (fun q : HeightOneSpectrum (𝓞 L) =>
      (q.adicCompletionIntegers L : Set (q.adicCompletion L)))
    tendsto_under_cofinite

private def globalIntegralAdeleEquiv :
    (𝓞 L ⊗[𝓞 K] FiniteAdeleRing (𝓞 K) K) ≃ FiniteAdeleRing (𝓞 L) L :=
  (adeleTensorRestrictedEquiv K L).toEquiv |>.trans
    (globalLocalRestrictedEquiv K L) |>.trans (globalFlattenEquiv K L)

private theorem globalIntegralAdeleEquiv_apply
    (z : 𝓞 L ⊗[𝓞 K] FiniteAdeleRing (𝓞 K) K) (q : HeightOneSpectrum (𝓞 L)) :
    globalIntegralAdeleEquiv K L z q =
      integralTensorComparison L (q.under (𝓞 K))
        (adeleTensorRestrictedEquiv K L z (q.under (𝓞 K))) ⟨q, liesOver_under q⟩ := rfl

private theorem globalIntegralAdeleEquiv_eq
    (z : 𝓞 L ⊗[𝓞 K] FiniteAdeleRing (𝓞 K) K) :
    globalIntegralAdeleEquiv K L z =
      finiteAdeleTensorMap K L (globalIntegralTransport K L z) := by
  apply FiniteAdeleRing.ext
  intro q
  induction z with
  | tmul b x =>
    rw [globalIntegralAdeleEquiv_apply, adeleTensorRestrictedEquiv_tmul,
      integralTensorComparison_tmul, globalIntegralTransport_tmul,
      finiteAdeleTensorMap_tmul_apply, ← IsScalarTower.algebraMap_apply]
    exact mul_comm _ _
  | add z w hz hw =>
    simp only [globalIntegralAdeleEquiv_apply, map_add, RestrictedProduct.add_apply,
      Pi.add_apply] at hz hw ⊢
    rw [hz, hw]
    rfl

/-- The canonical finite-adele tensor map is bijective for number fields in
independent universes. -/
theorem finiteAdeleTensorMapBijective_proof : FiniteAdeleTensorMapBijective.{u, v} := by
  intro K L _ _ _ _ _
  have h : (finiteAdeleTensorMap K L : _ → _) =
      (globalIntegralAdeleEquiv K L) ∘ (globalIntegralTransport K L).symm := by
    funext z
    simpa only [Function.comp_apply, LinearEquiv.apply_symm_apply] using
      (globalIntegralAdeleEquiv_eq K L ((globalIntegralTransport K L).symm z)).symm
  rw [h]
  exact (globalIntegralAdeleEquiv K L).bijective.comp
    (globalIntegralTransport K L).symm.bijective

end Langlands.Global.AdelicFunctoriality
