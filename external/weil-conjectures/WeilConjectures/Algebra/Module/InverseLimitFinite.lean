/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem

/-!
# Inverse limits of finite modules

A finiteness criterion used to control `ℓ`-adic cohomology `Hⁱ(X, ℤ_ℓ) = lim Hⁱ(X, ℤ/ℓᵐ)`
(the vanishing of `lim¹` for towers of finite groups is
`AddCommGroup.exists_sub_map_succ_eq_of_finite`):

* `PadicInt.module_finite_of_finite_quotient`: a `ℤ_p`-module `A` with maps `ρₘ : A ⟶ Eₘ` to
  modules killed by `pᵐ`, with `ker ρₘ = pᵐ A`, `⋂ ker ρₘ = 0` and `E₁` finite, is finitely
  generated. This applies to `A = Hⁱ(X, ℤ_ℓ)` with the reductions `ρₘ : Hⁱ(X, ℤ_ℓ) ⟶ Hⁱ(X, ℤ/ℓᵐ)`.

The proof is by compactness.
-/

@[expose] public section

open Topology Filter

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
  {E : ℕ → Type*} [∀ m, AddCommGroup (E m)] [∀ m, Module ℤ_[p] (E m)]

/-- A combination `∑ cₛ • ρ s` in a module killed by `pᵐ` only depends on the `cₛ` modulo `pᵐ`,
so it is locally constant in the coefficients. -/
lemma isLocallyConstant_sum_smul {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (hM : ∀ y : M, (p : ℤ_[p]) ^ m • y = 0) {ι : Type*} [Fintype ι] (v : ι → M) :
    IsLocallyConstant fun c : ι → ℤ_[p] ↦ ∑ i, c i • v i := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro c
  have hball : IsOpen (Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(m : ℤ)))) :=
    IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (by exact_mod_cast
      (Fact.out : p.Prime).ne_zero))
  have h (i : ι) : ∀ᶠ c' : ι → ℤ_[p] in 𝓝 c,
      c' i - c i ∈ Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(m : ℤ))) :=
    ((continuous_apply i).sub continuous_const).continuousAt.eventually
      (hball.mem_nhds (by simp))
  filter_upwards [eventually_all.2 h] with c' hc'
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hmem := hc' i
  rw [Metric.mem_closedBall, dist_zero_right, norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [← sub_add_cancel (c' i) (c i), add_smul, ← ha, mul_smul, hM, smul_zero, zero_add]

/-- **Finite generation from finite reduction.** Let `A` be a `ℤ_p`-module with maps
`ρₘ : A ⟶ Eₘ` to modules killed by `pᵐ`, such that `ker ρₘ ⊆ pᵐ A`, `⋂ₘ ker ρₘ = 0` and `E₁`
is finite. Then `A` is finitely generated.

Indeed `A / pA ↪ E₁` is finite, so finitely many elements `s` generate `A` modulo `pA`, hence
modulo every `pᵐ A`; the coefficients of an approximation of `a` modulo `pᵐ A` form a closed
nonempty subset `Cₘ` of the compact space `ℤ_pˢ`, and a point of `⋂ Cₘ` expresses `a`. -/
theorem module_finite_of_finite_quotient (ρ : ∀ m, A →ₗ[ℤ_[p]] E m)
    (hE : ∀ m (y : E m), (p : ℤ_[p]) ^ m • y = 0)
    (hker : ∀ m a, ρ m a = 0 → ∃ a', a = (p : ℤ_[p]) ^ m • a')
    (hsep : ∀ a, (∀ m, ρ m a = 0) → a = 0) [Finite (E 1)] : Module.Finite ℤ_[p] A := by
  classical
  -- finitely many elements represent `A` modulo `p A`
  have hR : (Set.range (ρ 1)).Finite := Set.toFinite _
  let g (y : E 1) : A := if h : ∃ a, ρ 1 a = y then h.choose else 0
  let s : Finset A := hR.toFinset.image g
  have hs (a : A) : ∃ t ∈ s, ∃ a', a = t + (p : ℤ_[p]) • a' := by
    have hy : ρ 1 a ∈ hR.toFinset := hR.mem_toFinset.2 ⟨a, rfl⟩
    set t := g (ρ 1 a)
    have ht : ρ 1 t = ρ 1 a := by
      have h : ∃ b, ρ 1 b = ρ 1 a := ⟨a, rfl⟩
      simp only [t, g, dite_eq_left h]
      exact h.choose_spec
    obtain ⟨a', ha'⟩ := hker 1 (a - t) (by rw [map_sub, ht, sub_self])
    refine ⟨t, Finset.mem_image.2 ⟨_, hy, rfl⟩, a', ?_⟩
    rw [← pow_one (p : ℤ_[p]), ← ha', add_sub_cancel]
  -- approximation modulo `pᵐ A`
  have happrox (m : ℕ) (a : A) : ∃ c : s → ℤ_[p], ∃ a',
      a = ∑ i, c i • (i : A) + (p : ℤ_[p]) ^ m • a' := by
    induction m generalizing a with
    | zero => exact ⟨0, a, by simp⟩
    | succ m ih =>
      obtain ⟨c, b, hb⟩ := ih a
      obtain ⟨t, ht, b', rfl⟩ := hs b
      refine ⟨c + Pi.single ⟨t, ht⟩ ((p : ℤ_[p]) ^ m), b', ?_⟩
      rw [hb, smul_add, smul_smul, ← pow_succ]
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      abel
  have hρ (m : ℕ) (b : A) : ρ m ((p : ℤ_[p]) ^ m • b) = 0 := by rw [map_smul, hE]
  refine ⟨⟨s, top_unique fun a _ ↦ ?_⟩⟩
  let C (m : ℕ) : Set (s → ℤ_[p]) := {c | ρ m (∑ i, c i • (i : A)) = ρ m a}
  have hC (m : ℕ) : IsClosed (C m) := by
    have hlc : IsLocallyConstant fun c : s → ℤ_[p] ↦ ρ m (∑ i, c i • (i : A)) := by
      simp only [map_sum, map_smul]
      exact isLocallyConstant_sum_smul (hE m) _
    exact hlc.isClosed_fiber _
  have hCne (m : ℕ) : (C m).Nonempty := by
    obtain ⟨c, a', ha'⟩ := happrox m a
    refine ⟨c, ?_⟩
    simp only [C, Set.mem_ofPred_eq]
    rw [ha', map_add, hρ, add_zero]
  have hCmono (m : ℕ) : C (m + 1) ⊆ C m := by
    intro c hc
    simp only [C, Set.mem_ofPred_eq] at hc ⊢
    rw [← sub_eq_zero, ← map_sub] at hc ⊢
    obtain ⟨b, hb⟩ := hker (m + 1) _ hc
    rw [hb, pow_succ', mul_smul, smul_comm, hρ]
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCmono
    hCne (hC 0).isCompact hC
  have heq : a = ∑ i, c i • (i : A) := by
    refine (sub_eq_zero.1 (hsep _ fun m ↦ ?_)).symm
    rw [map_sub, sub_eq_zero]
    exact Set.mem_iInter.1 hc m
  rw [heq]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span i.2)

end PadicInt
