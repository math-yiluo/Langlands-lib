import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff

/-! # A membership criterion for `C_H` (the structure of the proof of Proposition VI.3.1)

Waldspurger 2003, proof of Proposition VI.3.1 (printed pp. 302–305): to prove `f_ψ ∈ C_H`, "En
vertu de I.1 (4) et de l'égalité `M̄_0^+ = ⋃_{J ⊂ Δ_0} M̄_0^+(J)`" the seminorm `ν_r` is reduced to
the seminorms `ν_{r,J}` on the pieces `M̄_0^+(J)` of finitely many functions, and each `ν_{r,J}` is
bounded by `n(ϕ) + n^w(ϕ) + n^+(ϕ)` (the region `s(m) ⩽ t`, and the weak and positive parts of
the constant term on `s(m) ⩾ t`).

This module proves this reduction for abstract data:

* `IsRapidlyDecreasingOnSet`: `|f| ≤ c_r Ξ (1 + σ)^{−r}` on a set, for every `r`;
* its stability under restriction, finite unions and sums;
* `isRapidlyDecreasingOnSet_of_le_rpow`: the bound `n(ϕ)` from a bound in `1 + L` (for the
  source, `L = |H_G|`) on a region where `1 + σ ≤ C (1 + L)`;
* `isRapidlyDecreasingOnSet_univ_of_cartan`: I.1 (4) and the finiteness of the
  `K × K`-translates;
* `nu_lt_top_of_isRapidlyDecreasingOnSet_univ`, `mem_levelSubmodule_of_cartan`: rapid decay on
  all of `G` gives finite seminorms `ν_r`, hence membership in `C_H` for an `H`-bi-invariant
  function.
-/

noncomputable section

open scoped ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Rapid

variable {G : Type u} {Ξ σ : G → ℝ}

/-- `f` decreases rapidly on the set `S`: for every `r` there is `c` with
`‖f x‖ ≤ c Ξ(x) (1 + σ(x))^{−r}` for all `x ∈ S` (the bounds `ν_{r,J}`, `n(ϕ)`, `n^w(ϕ)`,
`n^+(ϕ)` of the proof of Proposition VI.3.1). -/
def IsRapidlyDecreasingOnSet (Ξ σ : G → ℝ) (S : Set G) (f : G → ℂ) : Prop :=
  ∀ r : ℝ, ∃ c : ℝ, ∀ x ∈ S, ‖f x‖ ≤ c * Ξ x * (1 + σ x) ^ (-r)

theorem IsRapidlyDecreasingOnSet.mono {S T : Set G} {f : G → ℂ}
    (h : IsRapidlyDecreasingOnSet Ξ σ S f) (hT : T ⊆ S) : IsRapidlyDecreasingOnSet Ξ σ T f :=
  fun r => (h r).imp fun _ hc x hx => hc x (hT hx)

/-- The constant may be taken nonnegative. -/
theorem IsRapidlyDecreasingOnSet.exists_nonneg (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {S : Set G} {f : G → ℂ} (h : IsRapidlyDecreasingOnSet Ξ σ S f) (r : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ S, ‖f x‖ ≤ c * Ξ x * (1 + σ x) ^ (-r) := by
  obtain ⟨c, hc⟩ := h r
  refine ⟨|c|, abs_nonneg c, fun x hx => (hc x hx).trans ?_⟩
  have hw : 0 ≤ Ξ x * (1 + σ x) ^ (-r) :=
    mul_nonneg (hΞ0 x) (Real.rpow_nonneg (by linarith [hσ0 x]) _)
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_abs_self c) hw

theorem IsRapidlyDecreasingOnSet.union (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {S T : Set G} {f : G → ℂ} (hS : IsRapidlyDecreasingOnSet Ξ σ S f)
    (hT : IsRapidlyDecreasingOnSet Ξ σ T f) : IsRapidlyDecreasingOnSet Ξ σ (S ∪ T) f := by
  intro r
  obtain ⟨c₁, hc₁0, hc₁⟩ := hS.exists_nonneg hΞ0 hσ0 r
  obtain ⟨c₂, hc₂0, hc₂⟩ := hT.exists_nonneg hΞ0 hσ0 r
  refine ⟨c₁ + c₂, fun x hx => ?_⟩
  have hw : 0 ≤ Ξ x * (1 + σ x) ^ (-r) :=
    mul_nonneg (hΞ0 x) (Real.rpow_nonneg (by linarith [hσ0 x]) _)
  rcases hx with hx | hx
  · calc ‖f x‖ ≤ c₁ * Ξ x * (1 + σ x) ^ (-r) := hc₁ x hx
      _ = c₁ * (Ξ x * (1 + σ x) ^ (-r)) := by ring
      _ ≤ (c₁ + c₂) * (Ξ x * (1 + σ x) ^ (-r)) :=
          mul_le_mul_of_nonneg_right (by linarith) hw
      _ = (c₁ + c₂) * Ξ x * (1 + σ x) ^ (-r) := by ring
  · calc ‖f x‖ ≤ c₂ * Ξ x * (1 + σ x) ^ (-r) := hc₂ x hx
      _ = c₂ * (Ξ x * (1 + σ x) ^ (-r)) := by ring
      _ ≤ (c₁ + c₂) * (Ξ x * (1 + σ x) ^ (-r)) :=
          mul_le_mul_of_nonneg_right (by linarith) hw
      _ = (c₁ + c₂) * Ξ x * (1 + σ x) ^ (-r) := by ring

/-- Rapid decay on finitely many sets gives rapid decay on their union. -/
theorem isRapidlyDecreasingOnSet_biUnion (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {ι : Type*} (s : Finset ι) (T : ι → Set G) {f : G → ℂ}
    (h : ∀ i ∈ s, IsRapidlyDecreasingOnSet Ξ σ (T i) f) :
    IsRapidlyDecreasingOnSet Ξ σ (⋃ i ∈ s, T i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => intro r; exact ⟨0, fun x hx => by simp at hx⟩
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i s)).union hΞ0 hσ0
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsRapidlyDecreasingOnSet.add (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {S : Set G} {f₁ f₂ : G → ℂ} (h₁ : IsRapidlyDecreasingOnSet Ξ σ S f₁)
    (h₂ : IsRapidlyDecreasingOnSet Ξ σ S f₂) : IsRapidlyDecreasingOnSet Ξ σ S (f₁ + f₂) := by
  intro r
  obtain ⟨c₁, -, hc₁⟩ := h₁.exists_nonneg hΞ0 hσ0 r
  obtain ⟨c₂, -, hc₂⟩ := h₂.exists_nonneg hΞ0 hσ0 r
  refine ⟨c₁ + c₂, fun x hx => ?_⟩
  calc ‖(f₁ + f₂) x‖ ≤ ‖f₁ x‖ + ‖f₂ x‖ := norm_add_le _ _
    _ ≤ c₁ * Ξ x * (1 + σ x) ^ (-r) + c₂ * Ξ x * (1 + σ x) ^ (-r) :=
        add_le_add (hc₁ x hx) (hc₂ x hx)
    _ = (c₁ + c₂) * Ξ x * (1 + σ x) ^ (-r) := by ring

/-- **The bound `n(ϕ)`** (proof of Proposition VI.3.1, "il existe `C > 0` tel que si `m`
vérifie `s(m) ⩽ t`, alors `1 + σ(m) ⩽ C(1 + |H_G(m)|)`"): a bound
`‖f‖ ≤ c_r Ξ (1 + L)^{−r}` for every `r` on `S`, where `1 + σ ≤ C (1 + L)`, gives rapid decay
on `S`. -/
theorem isRapidlyDecreasingOnSet_of_le_rpow (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {S : Set G} {f : G → ℂ} {L : G → ℝ} (hL0 : ∀ x ∈ S, 0 ≤ L x)
    (hL : ∃ C : ℝ, ∀ x ∈ S, 1 + σ x ≤ C * (1 + L x))
    (hb : ∀ r : ℝ, ∃ c : ℝ, ∀ x ∈ S, ‖f x‖ ≤ c * Ξ x * (1 + L x) ^ (-r)) :
    IsRapidlyDecreasingOnSet Ξ σ S f := by
  intro r
  obtain ⟨C₀, hC₀⟩ := hL
  set C : ℝ := max C₀ 1 with hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set t : ℝ := max r 0 with ht
  have ht0 : 0 ≤ t := le_max_right _ _
  obtain ⟨c, hc⟩ := hb t
  refine ⟨|c| * C ^ t, fun x hx => ?_⟩
  have h1 : 0 < 1 + σ x := by linarith [hσ0 x]
  have h2 : 0 < 1 + L x := by linarith [hL0 x hx]
  have hσx : 1 + σ x ≤ C * (1 + L x) :=
    (hC₀ x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2.le)
  have hdiv : (1 + σ x) / C ≤ 1 + L x := (div_le_iff₀' hCpos).mpr hσx
  have h4 : (1 + L x) ^ (-t) ≤ C ^ t * (1 + σ x) ^ (-t) := by
    calc (1 + L x) ^ (-t) ≤ ((1 + σ x) / C) ^ (-t) :=
          Real.rpow_le_rpow_of_nonpos (div_pos h1 hCpos) hdiv (neg_nonpos.mpr ht0)
      _ = C ^ t * (1 + σ x) ^ (-t) := by
          rw [Real.div_rpow h1.le hCpos.le, Real.rpow_neg hCpos.le, div_inv_eq_mul, mul_comm]
  have h5 : (1 + σ x) ^ (-t) ≤ (1 + σ x) ^ (-r) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hσ0 x]) (neg_le_neg (le_max_left r 0))
  have hCt : 0 ≤ C ^ t := Real.rpow_nonneg hCpos.le t
  calc ‖f x‖ ≤ c * Ξ x * (1 + L x) ^ (-t) := hc x hx
    _ ≤ |c| * Ξ x * (1 + L x) ^ (-t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c) (hΞ0 x))
          (Real.rpow_nonneg h2.le _)
    _ ≤ |c| * Ξ x * (C ^ t * (1 + σ x) ^ (-r)) :=
        mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left h5 hCt))
          (mul_nonneg (abs_nonneg c) (hΞ0 x))
    _ = |c| * C ^ t * Ξ x * (1 + σ x) ^ (-r) := by ring

end Rapid

section Cartan

variable {G : Type u} [Group G] {Ξ σ : G → ℝ}

/-- **Reduction to the chamber** (proof of Proposition VI.3.1, "En vertu de I.1 (4)"): if
`G = K S K`, `Ξ` and `σ` are bi-invariant under `K`, and the functions `x ↦ f(k₁ x k₂)`,
`k₁, k₂ ∈ K`, lie in a finite set `Ff` of functions decreasing rapidly on `S`, then `f`
decreases rapidly on `G`. -/
theorem isRapidlyDecreasingOnSet_univ_of_cartan (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {K : Subgroup G} {S : Set G} (hcartan : ∀ g : G, ∃ k₁ ∈ K, ∃ x ∈ S, ∃ k₂ ∈ K, g = k₁ * x * k₂)
    (hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, σ (k₁ * g * k₂) = σ g) {f : G → ℂ}
    (Ff : Finset (G → ℂ)) (hFf : ∀ k₁ ∈ K, ∀ k₂ ∈ K, (fun x => f (k₁ * x * k₂)) ∈ Ff)
    (hS : ∀ φ ∈ Ff, IsRapidlyDecreasingOnSet Ξ σ S φ) :
    IsRapidlyDecreasingOnSet Ξ σ Set.univ f := by
  classical
  intro r
  have hS' : ∀ φ ∈ Ff, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ S, ‖φ x‖ ≤ c * Ξ x * (1 + σ x) ^ (-r) :=
    fun φ hφ => (hS φ hφ).exists_nonneg hΞ0 hσ0 r
  choose! c hc0 hc using hS'
  refine ⟨∑ φ ∈ Ff, c φ, fun g _ => ?_⟩
  obtain ⟨k₁, hk₁, x, hx, k₂, hk₂, rfl⟩ := hcartan g
  have hφ := hFf k₁ hk₁ k₂ hk₂
  have hw : 0 ≤ Ξ x * (1 + σ x) ^ (-r) :=
    mul_nonneg (hΞ0 x) (Real.rpow_nonneg (by linarith [hσ0 x]) _)
  have hterm : c (fun x => f (k₁ * x * k₂)) ≤ ∑ φ ∈ Ff, c φ :=
    Finset.single_le_sum (f := c) (fun φ hφ => hc0 φ hφ) hφ
  rw [hΞK k₁ hk₁ k₂ hk₂, hσK k₁ hk₁ k₂ hk₂]
  calc ‖f (k₁ * x * k₂)‖ ≤ c (fun x => f (k₁ * x * k₂)) * Ξ x * (1 + σ x) ^ (-r) :=
        hc _ hφ x hx
    _ = c (fun x => f (k₁ * x * k₂)) * (Ξ x * (1 + σ x) ^ (-r)) := by ring
    _ ≤ (∑ φ ∈ Ff, c φ) * (Ξ x * (1 + σ x) ^ (-r)) := mul_le_mul_of_nonneg_right hterm hw
    _ = (∑ φ ∈ Ff, c φ) * Ξ x * (1 + σ x) ^ (-r) := by ring

omit [Group G] in
/-- Rapid decay on all of `G` gives finite seminorms: `ν_r(f) < ∞` for every `r`. -/
theorem nu_lt_top_of_isRapidlyDecreasingOnSet_univ (hΞ : ∀ g, 0 < Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {f : G → ℂ} (h : IsRapidlyDecreasingOnSet Ξ σ Set.univ f) (r : ℝ) : nu Ξ σ r f < ⊤ := by
  obtain ⟨c, hc⟩ := h r
  refine lt_of_le_of_lt (iSup_le fun g => ?_) (ENNReal.ofReal_lt_top (r := c))
  have h1 : 0 < 1 + σ g := by linarith [hσ0 g]
  have hw : 0 ≤ (Ξ g)⁻¹ * (1 + σ g) ^ r :=
    mul_nonneg (inv_nonneg.mpr (hΞ g).le) (Real.rpow_nonneg h1.le _)
  rw [weight, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := hc g (Set.mem_univ g)
  calc ‖f g‖ * ((Ξ g)⁻¹ * (1 + σ g) ^ r)
      ≤ c * Ξ g * (1 + σ g) ^ (-r) * ((Ξ g)⁻¹ * (1 + σ g) ^ r) :=
        mul_le_mul_of_nonneg_right hb hw
    _ = c * (Ξ g * (Ξ g)⁻¹) * ((1 + σ g) ^ (-r) * (1 + σ g) ^ r) := by ring
    _ = c := by
        rw [mul_inv_cancel₀ (hΞ g).ne', ← Real.rpow_add h1, neg_add_cancel, Real.rpow_zero,
          mul_one, mul_one]

/-- **Membership in `C_H`** (the conclusion of the proof of Proposition VI.3.1): an
`H`-bi-invariant function satisfying the hypotheses of `isRapidlyDecreasingOnSet_univ_of_cartan`
lies in `levelSubmodule Ξ σ H`. -/
theorem mem_levelSubmodule_of_cartan (hΞ : ∀ g, 0 < Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    {H K : Subgroup G} {S : Set G}
    (hcartan : ∀ g : G, ∃ k₁ ∈ K, ∃ x ∈ S, ∃ k₂ ∈ K, g = k₁ * x * k₂)
    (hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, σ (k₁ * g * k₂) = σ g) {f : G → ℂ}
    (hf : IsBiInvariant H f) (Ff : Finset (G → ℂ))
    (hFf : ∀ k₁ ∈ K, ∀ k₂ ∈ K, (fun x => f (k₁ * x * k₂)) ∈ Ff)
    (hS : ∀ φ ∈ Ff, IsRapidlyDecreasingOnSet Ξ σ S φ) : f ∈ levelSubmodule Ξ σ H :=
  ⟨hf, nu_lt_top_of_isRapidlyDecreasingOnSet_univ hΞ hσ0
    (isRapidlyDecreasingOnSet_univ_of_cartan (fun g => (hΞ g).le) hσ0 hcartan hΞK hσK Ff hFf
      hS)⟩

end Cartan

end Langlands.HarishChandraSchwartz
