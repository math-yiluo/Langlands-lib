import Langlands.Cohomology.ModuleComplex.ObstructionConeOpenStatement
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Transport of obstruction-cone data along a quasi-isomorphism

Let `φ : K → C` be a chain map that induces injective and surjective maps on first and
second cohomology after tensoring with the relevant modules. The cochains `z` and `θ` of
an obstruction cone over `C` are replaced by cochains `zh` and `θh` over `K`, and the
vanishing of first cohomology of the two cones is compared.
-/

set_option autoImplicit false

universe u

open TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.ObstructionCone.Transfer

variable {A : Type u} [CommRing A]

/-- Tensoring with maps on the two sides commutes. -/
lemma rTensor_lTensor {X Y N N' : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (f : X →ₗ[A] Y) (g : N →ₗ[A] N') (t : X ⊗[A] N) :
    f.rTensor N' (g.lTensor X t) = g.lTensor Y (f.rTensor N t) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

/-- First and second cohomology comparison data for `- ⊗[A] N`. -/
def CohIso (K C : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
    (dK : ∀ i, K i →ₗ[A] K (i + 1)) (d : ∀ i, C i →ₗ[A] C (i + 1)) (φ : ∀ i, K i →ₗ[A] C i)
    (N : Type u) [AddCommGroup N] [Module A N] : Prop :=
  (∀ (i : ℕ) (x : K (i + 1) ⊗[A] N), (dK (i + 1)).rTensor N x = 0 →
      (φ (i + 1)).rTensor N x ∈ LinearMap.range ((d i).rTensor N) →
        x ∈ LinearMap.range ((dK i).rTensor N)) ∧
    (∀ (i : ℕ) (y : C (i + 1) ⊗[A] N), (d (i + 1)).rTensor N y = 0 →
      ∃ x : K (i + 1) ⊗[A] N, (dK (i + 1)).rTensor N x = 0 ∧
        (φ (i + 1)).rTensor N x - y ∈ LinearMap.range ((d i).rTensor N))

variable {K C : ℕ → Type u} [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
  {dK : ∀ i, K i →ₗ[A] K (i + 1)} {d : ∀ i, C i →ₗ[A] C (i + 1)} {φ : ∀ i, K i →ₗ[A] C i}
  {F Q : Type u} [AddCommGroup F] [Module A F] [AddCommGroup Q] [Module A Q]

/-- A chain map commutes with the differentials after tensoring with a module. -/
lemma rTensor_chain (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ dK i) (N : Type u) [AddCommGroup N]
    [Module A N] (i : ℕ) (x : K i ⊗[A] N) :
    (d i).rTensor N ((φ i).rTensor N x) = (φ (i + 1)).rTensor N ((dK i).rTensor N x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hφ, LinearMap.rTensor_comp,
    LinearMap.comp_apply]

/-- The cochains `z` and `θ` are cohomologous to images of cochains over `K`. -/
theorem exists_transfer (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ dK i)
    (hQ : CohIso K C dK d φ Q) (hF : CohIso K C dK d φ F)
    (δ : Q →ₗ[A] F) (θ : C 1 ⊗[A] F) (z : C 2 ⊗[A] Q)
    (hθ : (d 1).rTensor F θ = δ.lTensor (C 2) z) (hz : (d 2).rTensor Q z = 0) :
    ∃ (zh : K 2 ⊗[A] Q) (w : C 1 ⊗[A] Q) (θh : K 1 ⊗[A] F) (v : C 0 ⊗[A] F),
      (dK 2).rTensor Q zh = 0 ∧ (φ 2).rTensor Q zh = z + (d 1).rTensor Q w ∧
      (dK 1).rTensor F θh = δ.lTensor (K 2) zh ∧
      (φ 1).rTensor F θh = θ + δ.lTensor (C 1) w + (d 0).rTensor F v := by
  obtain ⟨zh, hzh, w, hw⟩ := hQ.2 1 z hz
  have hφzh : (φ 2).rTensor Q zh = z + (d 1).rTensor Q w := by rw [hw]; abel
  have hc₂ : (dK 2).rTensor F (δ.lTensor (K 2) zh) = 0 := by
    rw [rTensor_lTensor, hzh, map_zero]
  have hφc₂ : (φ 2).rTensor F (δ.lTensor (K 2) zh) =
      (d 1).rTensor F (θ + δ.lTensor (C 1) w) := by
    rw [rTensor_lTensor, hφzh, map_add, map_add, hθ, ← rTensor_lTensor]
  obtain ⟨θ₀, hθ₀⟩ := hF.1 1 _ hc₂ ⟨_, hφc₂.symm⟩
  have hy₁ : (d 1).rTensor F ((φ 1).rTensor F θ₀ - θ - δ.lTensor (C 1) w) = 0 := by
    rw [map_sub, map_sub, rTensor_chain hφ, hθ₀, hφc₂, map_add]
    abel
  obtain ⟨t, ht, v', hv'⟩ := hF.2 0 _ hy₁
  refine ⟨zh, w, θ₀ - t, -v', hzh, hφzh, ?_, ?_⟩
  · rw [map_sub, hθ₀, ht, sub_zero]
  · rw [map_sub, map_neg, hv']
    abel


section Compare

variable (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ dK i)
  (δ : Q →ₗ[A] F) (θ : C 1 ⊗[A] F) (z : C 2 ⊗[A] Q)
  (zh : K 2 ⊗[A] Q) (w : C 1 ⊗[A] Q) (θh : K 1 ⊗[A] F) (v : C 0 ⊗[A] F)
  (hzh : (dK 2).rTensor Q zh = 0) (hφzh : (φ 2).rTensor Q zh = z + (d 1).rTensor Q w)
  (hθh : (dK 1).rTensor F θh = δ.lTensor (K 2) zh)
  (hφθh : (φ 1).rTensor F θh = θ + δ.lTensor (C 1) w + (d 0).rTensor F v)
include hφ hzh hφzh hθh hφθh

omit hθh in
/-- Vanishing over `K` implies vanishing over `C`. -/
theorem hOneVanishes_of_model (M : Type u) [AddCommGroup M] [Module A M]
    (hM : CohIso K C dK d φ M) (h : HOneVanishes K dK δ θh zh M) :
    HOneVanishes C d δ θ z M := by
  intro c ψ hc
  -- a cocycle over `K` lifting `c`
  have hm₂ : (dK 2).rTensor M (ψ.lTensor (K 2) zh) = 0 := by
    rw [rTensor_lTensor, hzh, map_zero]
  have hz' : ψ.lTensor (C 2) z = -(d 1).rTensor M c := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hc
  have hφm₂ : (φ 2).rTensor M (ψ.lTensor (K 2) zh) =
      (d 1).rTensor M (ψ.lTensor (C 1) w - c) := by
    rw [rTensor_lTensor, hφzh, map_add, map_sub, ← rTensor_lTensor, hz']
    abel
  obtain ⟨c₀, hc₀⟩ := hM.1 1 _ hm₂ ⟨_, hφm₂.symm⟩
  have hy₁ : (d 1).rTensor M ((φ 1).rTensor M (-c₀) - (c - ψ.lTensor (C 1) w)) = 0 := by
    rw [map_sub, rTensor_chain hφ, map_neg, hc₀, map_neg, hφm₂, map_sub, map_sub]
    abel
  obtain ⟨t, ht, e', he'⟩ := hM.2 0 _ hy₁
  have hĉ : (dK 1).rTensor M (-c₀ - t) + ψ.lTensor (K 2) zh = 0 := by
    rw [map_sub, ht, map_neg, hc₀]
    abel
  obtain ⟨bh, D, hbh, hD⟩ := h (-c₀ - t) ψ hĉ
  refine ⟨(φ 0).rTensor M bh + D.lTensor (C 0) v + e', D, ?_, hD⟩
  have hψ : ψ = -(D ∘ₗ δ) := eq_neg_of_add_eq_zero_left hD
  have he'' : (d 0).rTensor M e' =
      (φ 1).rTensor M t - ((φ 1).rTensor M (-c₀) - (c - ψ.lTensor (C 1) w)) := he'
  have key : (φ 1).rTensor M (-c₀ - t) = c - ψ.lTensor (C 1) w - (d 0).rTensor M e' := by
    rw [map_sub, he'']
    abel
  have := congrArg ((φ 1).rTensor M) hbh
  rw [key, map_add, ← rTensor_chain hφ, rTensor_lTensor, hφθh, map_add, map_add,
    ← rTensor_lTensor, hψ, LinearMap.lTensor_neg, LinearMap.neg_apply,
    ← LinearMap.comp_apply (D.lTensor (C 1)), ← LinearMap.lTensor_comp] at this
  rw [map_add, map_add]
  rw [show c = (c - -((D ∘ₗ δ).lTensor (C 1) w) - (d 0).rTensor M e') -
      (D ∘ₗ δ).lTensor (C 1) w + (d 0).rTensor M e' by abel, this]
  abel

omit hzh in
/-- Vanishing over `C` implies vanishing over `K`. -/
theorem hOneVanishes_model (M : Type u) [AddCommGroup M] [Module A M]
    (hM : CohIso K C dK d φ M) (h : HOneVanishes C d δ θ z M) :
    HOneVanishes K dK δ θh zh M := by
  intro ch ψ hch
  have hc : (d 1).rTensor M ((φ 1).rTensor M ch + ψ.lTensor (C 1) w) + ψ.lTensor (C 2) z = 0 := by
    have := congrArg ((φ 2).rTensor M) hch
    rw [map_add, ← rTensor_chain hφ, rTensor_lTensor, hφzh, map_add, map_zero] at this
    rw [map_add, rTensor_lTensor, ← this]
    abel
  obtain ⟨b, D, hb, hD⟩ := h _ ψ hc
  have hψ : ψ = -(D ∘ₗ δ) := eq_neg_of_add_eq_zero_left hD
  have hcyc : (dK 1).rTensor M (ch - D.lTensor (K 1) θh) = 0 := by
    rw [map_sub, rTensor_lTensor, hθh, ← LinearMap.comp_apply (D.lTensor (K 2)),
      ← LinearMap.lTensor_comp, eq_neg_of_add_eq_zero_left hch, hψ, LinearMap.lTensor_neg,
      LinearMap.neg_apply]
    abel
  have hbd : (φ 1).rTensor M (ch - D.lTensor (K 1) θh) =
      (d 0).rTensor M (b - D.lTensor (C 0) v) := by
    rw [map_sub, rTensor_lTensor, hφθh, map_add, map_add, map_sub, ← rTensor_lTensor,
      ← LinearMap.comp_apply (D.lTensor (C 1)) (δ.lTensor (C 1)), ← LinearMap.lTensor_comp]
    have hb' : (φ 1).rTensor M ch = (d 0).rTensor M b + D.lTensor (C 1) θ -
        ψ.lTensor (C 1) w := by rw [← hb]; abel
    rw [hb', hψ, LinearMap.lTensor_neg, LinearMap.neg_apply]
    abel
  obtain ⟨bh, hbh⟩ := hM.1 0 _ hcyc ⟨_, hbd.symm⟩
  refine ⟨bh, D, ?_, hD⟩
  rw [hbh]
  abel

end Compare

end Langlands.Cohomology.ModuleComplex.ObstructionCone.Transfer
