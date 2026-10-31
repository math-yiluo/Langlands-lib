/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Adapted by Worker 137 from Anthropic FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_projective_complex_forall_baseChange_quasiIso_cech_of_locallyTrivial.lean.
Changes: use published algebra adapters; retain original-base cycle tests;
move helpers to the host namespace; remove P2M utilities and attribute resets;
use host imports, finite port options, and ordinary instance lets.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Langlands.AlgebraicGeometry.Modules.NoetherianCechProjectiveRepresentativeStatement
import Langlands.Cohomology.ModuleComplex.BoundedFlatComplexProjectiveProof
import Langlands.Cohomology.ModuleComplex.BoundedFlatQuasiIsoBaseChangeProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules

namespace CechProjectiveTransport

section Transport

variable {A : Type u} [CommRing A]
  {K : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  {P : ℕ → Type u} [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
  {Q : ℕ → Type u} [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]
  (δ : ∀ i, K i →ₗ[A] K (i + 1)) (dP : ∀ i, P i →ₗ[A] P (i + 1)) (dQ : ∀ i, Q i →ₗ[A] Q (i + 1))
  (ψ : ∀ i, K i →ₗ[A] P i) (E : ∀ i, P i ≃ₗ[A] Q i)

lemma E_dP (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ) (x : P i) :
    E (i + 1) (dP i x) = dQ i (E i x) := by
  have h := congrArg (fun f : P i →ₗ[A] Q (i + 1) => f x) (hE i)
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] using h

lemma Esymm_dQ (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ) (y : Q i) :
    (E (i + 1)).symm (dQ i y) = dP i ((E i).symm y) := by
  apply (E (i + 1)).injective
  rw [LinearEquiv.apply_symm_apply, E_dP dP dQ E hE, LinearEquiv.apply_symm_apply]

lemma transport_comm (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap)
    (hψ : ∀ i, dP i ∘ₗ ψ i = ψ (i + 1) ∘ₗ δ i) (i : ℕ) :
    ((E (i + 1)).toLinearMap ∘ₗ ψ (i + 1)) ∘ₗ δ i = dQ i ∘ₗ ((E i).toLinearMap ∘ₗ ψ i) := by
  rw [LinearMap.comp_assoc, ← hψ i, ← LinearMap.comp_assoc, hE i, LinearMap.comp_assoc]

lemma transport_h0inj
    (h0inj : ∀ x : K 0, δ 0 x = 0 → ψ 0 x = 0 → x = 0) (x : K 0) (hx : δ 0 x = 0)
    (hx' : ((E 0).toLinearMap ∘ₗ ψ 0) x = 0) : x = 0 := by
  apply h0inj x hx
  have : E 0 (ψ 0 x) = 0 := hx'
  exact (E 0).map_eq_zero_iff.1 this

lemma transport_h0surj (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap)
    (h0surj : ∀ y : P 0, dP 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ ψ 0 x = y) (y : Q 0) (hy : dQ 0 y = 0) :
    ∃ x : K 0, δ 0 x = 0 ∧ ((E 0).toLinearMap ∘ₗ ψ 0) x = y := by
  have hy' : dP 0 ((E 0).symm y) = 0 := by
    rw [← Esymm_dQ dP dQ E hE, hy, map_zero]
  obtain ⟨x, hx, hxy⟩ := h0surj _ hy'
  refine ⟨x, hx, ?_⟩
  show E 0 (ψ 0 x) = y
  rw [hxy, LinearEquiv.apply_symm_apply]

lemma transport_hinj (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ)
    (hinj : ∀ x : K (i + 1), δ (i + 1) x = 0 → ψ (i + 1) x ∈ LinearMap.range (dP i) → x ∈ LinearMap.range (δ i))
    (x : K (i + 1)) (hx : δ (i + 1) x = 0)
    (hx' : ((E (i + 1)).toLinearMap ∘ₗ ψ (i + 1)) x ∈ LinearMap.range (dQ i)) : x ∈ LinearMap.range (δ i) := by
  apply hinj x hx
  obtain ⟨z, hz⟩ := hx'
  refine ⟨(E i).symm z, ?_⟩
  apply (E (i + 1)).injective
  rw [E_dP dP dQ E hE, LinearEquiv.apply_symm_apply, hz]
  rfl

lemma transport_hsurj (hE : ∀ i, (E (i + 1)).toLinearMap ∘ₗ dP i = dQ i ∘ₗ (E i).toLinearMap) (i : ℕ)
    (hsurj : ∀ y : P (i + 1), dP (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ ψ (i + 1) x - y ∈ LinearMap.range (dP i))
    (y : Q (i + 1)) (hy : dQ (i + 1) y = 0) :
    ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ ((E (i + 1)).toLinearMap ∘ₗ ψ (i + 1)) x - y ∈ LinearMap.range (dQ i) := by
  have hy' : dP (i + 1) ((E (i + 1)).symm y) = 0 := by
    rw [← Esymm_dQ dP dQ E hE, hy, map_zero]
  obtain ⟨x, hx, ⟨w, hw⟩⟩ := hsurj _ hy'
  refine ⟨x, hx, ⟨E i w, ?_⟩⟩
  rw [← E_dP dP dQ E hE, hw, map_sub, LinearEquiv.apply_symm_apply]
  rfl

end Transport

theorem isEmpty_idx {V : Scheme.{u}} (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    IsEmpty (K.Idx i) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  simp only [Fintype.card_fin] at this
  omega

theorem subsingleton_cochain {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    Subsingleton (F.cochain K i) := by
  let := isEmpty_idx K hi
  infer_instance

end CechProjectiveTransport

theorem noetherianCechProjectiveRepresentative :
    NoetherianCechProjectiveRepresentativeStatement.{u} := by
  intro R _ _ X π _ _ M htriv 𝒰 n hn
  classical

  let hflat : ∀ i, Module.Flat R ((OModulePresheaf.ofModules π M).cochain 𝒰 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial π M htriv 𝒰 i
  have hfinC : (OModulePresheaf.ofModules π M).CechFinite 𝒰 :=
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M htriv 𝒰
  have hCbdd : ∀ i, n < i → Subsingleton ((OModulePresheaf.ofModules π M).cochain 𝒰 i) := fun i hi =>
    CechProjectiveTransport.subsingleton_cochain (OModulePresheaf.ofModules π M) 𝒰 (by omega)

  obtain ⟨K, instACG, instMod, hKfin, hKproj, δ, hδδ, hKbdd, φ, hφ, h0inj, h0surj, hinj, hsurj⟩ :=
    Langlands.Cohomology.ModuleComplex.boundedFlatComplexProjective R (fun i => (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (fun i => (OModulePresheaf.ofModules π M).d 𝒰 i) (fun i => (OModulePresheaf.ofModules π M).d_comp_d 𝒰 i) n hCbdd
      hfinC.1 hfinC.2

  have hE := fun (A : Type u) [CommRing A] [Algebra R A] =>
    OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv A
  refine ⟨K, instACG, instMod, hKfin, hKproj, δ, hδδ, hKbdd, φ, hφ,
    fun A _ _ i => ((hE A).choose i).toLinearMap ∘ₗ (φ i).baseChange A,
    h0inj, h0surj, hinj, hsurj, fun A _ _ => ?_⟩
  obtain ⟨hEd, hEtmul⟩ := (hE A).choose_spec

  obtain ⟨hA0inj, hA0surj, hAinj, hAsurj⟩ :=
    Langlands.Cohomology.ModuleComplex.boundedFlatQuasiIsoBaseChange R K δ hδδ (fun i => (OModulePresheaf.ofModules π M).cochain 𝒰 i)
      (fun i => (OModulePresheaf.ofModules π M).d 𝒰 i) (fun i => (OModulePresheaf.ofModules π M).d_comp_d 𝒰 i) n hKbdd
      hCbdd φ hφ h0inj h0surj hinj hsurj A
  have hφA : ∀ i, ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A ∘ₗ (φ i).baseChange A
      = (φ (i + 1)).baseChange A ∘ₗ (δ i).baseChange A := by
    intro i; rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hφ i]
  refine ⟨fun i => CechProjectiveTransport.transport_comm (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd hφA i,
    fun i a k s => ?_,
    fun x hx hx' => CechProjectiveTransport.transport_h0inj (fun i => (δ i).baseChange A) (fun i => (φ i).baseChange A) _ hA0inj x hx hx',
    fun y hy => CechProjectiveTransport.transport_h0surj (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd hA0surj y hy,
    fun i x hx hx' => CechProjectiveTransport.transport_hinj (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd i (hAinj i) x hx hx',
    fun i y hy => CechProjectiveTransport.transport_hsurj (fun i => (δ i).baseChange A)
      (fun i => ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A) _ (fun i => (φ i).baseChange A) _ hEd i (hAsurj i) y hy⟩

  rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEtmul]


end Langlands.AlgebraicGeometry.Modules
