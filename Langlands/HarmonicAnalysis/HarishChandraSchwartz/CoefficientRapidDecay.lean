import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff

/-! # Reduction of Corollary III.1.2 to exponential bounds on the positive chamber

Waldspurger 2003, proof of Corollary III.1.2 (printed p. 264): "Grâce à I.1 (4) et à un argument
de `K`-finitude, on peut se limiter à démontrer l'inégalité pour `g ∈ M̄_0^+ ∩ G¹`", and, once
the coefficient is bounded by `C Ξ(a) (1 + σ(a))^d q^{−εσ(a)}`, "Pour tout `r ∈ ℝ`, il existe donc
`c > 0` tel que la fonction (1) soit majorée par `c Ξ(a) (1 + σ(a))^{−r}`".

This module proves these two reductions for abstract data:

* `exists_exp_neg_le_rpow`: `e^{−ε x} ≤ K (1 + x)^{−t}` for `x ≥ 0`;
* `IsExpDecreasingOn`: the bound `|F| ≤ C Ξ e^{−ε ‖H‖}` on a set;
* `exists_rpow_bound_of_exp_bound`: exponential bounds `C Ξ e^{−ε ‖H‖}` on finitely many sets
  covering `S`, with `1 + σ ≤ c (1 + ‖H‖)` on `S`, give `c_r Ξ (1 + σ)^{−r}` on `S` for every `r`;
* `isRapidlyDecreasingOn_of_cartan`: a coefficient `g ↦ ℓ(ρ(g) v)` is rapidly decreasing on a
  subgroup `N ⊆ K S K` (I.1 (4)) when `Ξ`, `σ` are `K`-bi-invariant and the finitely many
  coefficients `ℓ'(ρ(·) v')`, `v' ∈ ρ(K) v`, `ℓ' ∈ ℓ ∘ ρ(K)` (`K`-finiteness), decrease rapidly
  on `S`;
* `isRapidlyDecreasingOn_of_cartan_of_exp`: the combination.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

universe u v

section Elementary

/-- For `ε > 0` and every `t` there is `K ≥ 0` with `e^{−ε x} ≤ K (1 + x)^{−t}` for all
`x ≥ 0`. -/
theorem exists_exp_neg_le_rpow {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → Real.exp (-(ε * x)) ≤ K * (1 + x) ^ (-t) := by
  set n : ℕ := ⌈max t 0⌉₊ with hn
  have htn : t ≤ n := (le_max_left t 0).trans (Nat.le_ceil _)
  set M : ℝ := max 1 (n / ε) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨M ^ n, pow_nonneg (zero_le_one.trans hM1) n, fun x hx => ?_⟩
  have hx1 : 1 ≤ 1 + x := by linarith
  have hpos : 0 < 1 + x := by linarith
  -- `(1 + x)^n ≤ M^n e^{ε x}`
  have hkey : (1 + x) ^ n ≤ M ^ n * Real.exp (ε * x) := by
    rcases Nat.eq_zero_or_pos n with h0 | hnpos
    · rw [h0, pow_zero, pow_zero, one_mul]
      exact Real.one_le_exp (mul_nonneg hε.le hx)
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have h1 : 1 + x ≤ M * (1 + ε * x / n) := by
        have hMn : n / ε ≤ M := le_max_right _ _
        have hMe : 1 ≤ M * ε / n := by
          rw [le_div_iff₀ hnR, one_mul]
          calc (n : ℝ) = n / ε * ε := by field_simp
            _ ≤ M * ε := mul_le_mul_of_nonneg_right hMn hε.le
        have : M * (1 + ε * x / n) = M + M * ε / n * x := by ring
        rw [this]
        nlinarith
      have h2 : (1 + ε * x / n) ^ n ≤ Real.exp (ε * x) := by
        calc (1 + ε * x / n) ^ n ≤ Real.exp (ε * x / n) ^ n := by
              refine pow_le_pow_left₀ (by positivity) ?_ n
              linarith [Real.add_one_le_exp (ε * x / n)]
          _ = Real.exp (ε * x) := by
              rw [← Real.exp_nat_mul]
              congr 1
              field_simp
      calc (1 + x) ^ n ≤ (M * (1 + ε * x / n)) ^ n := pow_le_pow_left₀ hpos.le h1 n
        _ = M ^ n * (1 + ε * x / n) ^ n := mul_pow _ _ _
        _ ≤ M ^ n * Real.exp (ε * x) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (zero_le_one.trans hM1) n)
  have hexp : Real.exp (-(ε * x)) ≤ M ^ n * (1 + x) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, Real.exp_neg]
    have hp : 0 < (1 + x) ^ n := pow_pos hpos n
    rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
    calc (1 + x) ^ n * (Real.exp (ε * x))⁻¹
        ≤ M ^ n * Real.exp (ε * x) * (Real.exp (ε * x))⁻¹ :=
          mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (Real.exp_pos _).le)
      _ = M ^ n := by rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
  refine hexp.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (zero_le_one.trans hM1) n))
  exact Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg htn)

/-- `F` decays exponentially on `T` relative to `Ξ` and `H`: `|F(x)| ≤ C Ξ(x) e^{−ε ‖H(x)‖}` on `T`
for some `ε > 0` and `C` (the form of the bound `|χ(a)| ⩽ C₃ q^{−εσ(a)}` in the proof of
Corollary III.1.2, and of Lemma VI.2.3). -/
def IsExpDecreasingOn {X : Type*} {E : Type*} [SeminormedAddCommGroup E] (Ξ : X → ℝ)
    (H : X → E) (T : Set X) (F : X → ℂ) : Prop :=
  ∃ ε > 0, ∃ C : ℝ, ∀ x ∈ T, ‖F x‖ ≤ C * Ξ x * Real.exp (-(ε * ‖H x‖))

/-- **Exponential bounds on a finite cover give rapid decay** (end of the proof of Corollary
III.1.2): if `S` is covered by finitely many sets `T i` on each of which
`|F| ≤ C_i Ξ e^{−ε_i ‖H‖}`, and `1 + σ ≤ c (1 + ‖H‖)` on `S`, then for every `r` there is
`c_r` with `|F| ≤ c_r Ξ (1 + σ)^{−r}` on `S`. -/
theorem exists_rpow_bound_of_exp_bound {X : Type*} {E : Type*} [SeminormedAddCommGroup E]
    {S : Set X} {Ξ σ : X → ℝ} {H : X → E} {F : X → ℂ} (hΞ0 : ∀ x ∈ S, 0 ≤ Ξ x)
    (hσ0 : ∀ x ∈ S, 0 ≤ σ x) (hσH : ∃ c : ℝ, ∀ x ∈ S, 1 + σ x ≤ c * (1 + ‖H x‖))
    {ι : Type*} (s : Finset ι) (T : ι → Set X) (hcover : S ⊆ ⋃ i ∈ s, T i)
    (hexp : ∀ i ∈ s, IsExpDecreasingOn Ξ H (T i) F) (r : ℝ) :
    ∃ c : ℝ, ∀ x ∈ S, ‖F x‖ ≤ c * Ξ x * (1 + σ x) ^ (-r) := by
  classical
  obtain ⟨c₀, hc₀⟩ := hσH
  set c₁ : ℝ := max c₀ 1 with hc₁
  have hc₁pos : 0 < c₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set t : ℝ := max r 0 with ht
  have ht0 : 0 ≤ t := le_max_right _ _
  simp only [IsExpDecreasingOn] at hexp
  choose! ε hε C hC using hexp
  have hK' : ∀ i ∈ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y →
      Real.exp (-(ε i * y)) ≤ K * (1 + y) ^ (-t) := fun i hi => exists_exp_neg_le_rpow (hε i hi) t
  choose! K hK0 hKb using hK'
  refine ⟨∑ i ∈ s, |C i| * K i * c₁ ^ t, fun x hx => ?_⟩
  obtain ⟨i, hi, hxT⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hσx0 := hσ0 x hx
  have hΞx := hΞ0 x hx
  have hb : 0 < 1 + σ x := by linarith
  have hH1 : 0 < 1 + ‖H x‖ := by linarith [norm_nonneg (H x)]
  have hσx : 1 + σ x ≤ c₁ * (1 + ‖H x‖) :=
    (hc₀ x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH1.le)
  have hdiv : (1 + σ x) / c₁ ≤ 1 + ‖H x‖ := (div_le_iff₀' hc₁pos).mpr hσx
  have h4 : (1 + ‖H x‖) ^ (-t) ≤ c₁ ^ t * (1 + σ x) ^ (-t) := by
    calc (1 + ‖H x‖) ^ (-t) ≤ ((1 + σ x) / c₁) ^ (-t) :=
          Real.rpow_le_rpow_of_nonpos (div_pos hb hc₁pos) hdiv (neg_nonpos.mpr ht0)
      _ = c₁ ^ t * (1 + σ x) ^ (-t) := by
          rw [Real.div_rpow hb.le hc₁pos.le, Real.rpow_neg hc₁pos.le, div_inv_eq_mul, mul_comm]
  have h5 : (1 + σ x) ^ (-t) ≤ (1 + σ x) ^ (-r) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (le_max_left r 0))
  have hKi := hK0 i hi
  have hct : 0 ≤ c₁ ^ t := Real.rpow_nonneg hc₁pos.le t
  have hterm : |C i| * K i * c₁ ^ t ≤ ∑ j ∈ s, |C j| * K j * c₁ ^ t :=
    Finset.single_le_sum (f := fun j => |C j| * K j * c₁ ^ t)
      (fun j hj => mul_nonneg (mul_nonneg (abs_nonneg _) (hK0 j hj)) hct) hi
  have hr : 0 ≤ (1 + σ x) ^ (-r) := Real.rpow_nonneg hb.le _
  calc ‖F x‖ ≤ C i * Ξ x * Real.exp (-(ε i * ‖H x‖)) := hC i hi x hxT
    _ ≤ |C i| * Ξ x * (K i * (1 + ‖H x‖) ^ (-t)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hΞx)
          (hKb i hi _ (norm_nonneg _)) (Real.exp_pos _).le
          (mul_nonneg (abs_nonneg _) hΞx)
    _ ≤ |C i| * Ξ x * (K i * (c₁ ^ t * (1 + σ x) ^ (-r))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h4.trans ?_) hKi)
          (mul_nonneg (abs_nonneg _) hΞx)
        exact mul_le_mul_of_nonneg_left h5 hct
    _ = |C i| * K i * c₁ ^ t * (Ξ x * (1 + σ x) ^ (-r)) := by ring
    _ ≤ (∑ j ∈ s, |C j| * K j * c₁ ^ t) * (Ξ x * (1 + σ x) ^ (-r)) :=
        mul_le_mul_of_nonneg_right hterm (mul_nonneg hΞx hr)
    _ = (∑ j ∈ s, |C j| * K j * c₁ ^ t) * Ξ x * (1 + σ x) ^ (-r) := by ring

end Elementary

section Cartan

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- **Reduction to the positive chamber** (proof of Corollary III.1.2, "Grâce à I.1 (4) et à un
argument de `K`-finitude"): let `N` be a subgroup with `N ⊆ K S K` for a subgroup `K` and a set
`S`, `Ξ ≥ 0` and `σ ≥ 0` bi-invariant under `K`, and `v`, `ℓ` with finite sets `Vf ∋ ρ(k) v` and
`Lf ∋ ℓ ∘ ρ(k)` for `k ∈ K`. If every coefficient `s ↦ ℓ'(ρ(s) v')`, `v' ∈ Vf`, `ℓ' ∈ Lf`,
decreases rapidly on `S`, then `g ↦ ℓ(ρ(g) v)` decreases rapidly on `N`. -/
theorem isRapidlyDecreasingOn_of_cartan (ρ : Representation ℂ G V) {Ξ σ : G → ℝ}
    (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g) {N K : Subgroup G} {S : Set G}
    (hcartan : ∀ n ∈ N, ∃ k₁ ∈ K, ∃ x ∈ S, ∃ k₂ ∈ K, n = k₁ * x * k₂)
    (hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, σ (k₁ * g * k₂) = σ g) (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (Vf : Finset V) (Lf : Finset (V →ₗ[ℂ] ℂ)) (hVf : ∀ k ∈ K, ρ k v ∈ Vf)
    (hLf : ∀ k ∈ K, ℓ ∘ₗ ρ k ∈ Lf)
    (hS : ∀ v' ∈ Vf, ∀ ℓ' ∈ Lf, ∀ r : ℝ, ∃ c : ℝ, ∀ x ∈ S,
      ‖ℓ' (ρ x v')‖ ≤ c * Ξ x * (1 + σ x) ^ (-r)) :
    IsRapidlyDecreasingOn Ξ σ N (fun g => ℓ (ρ g v)) := by
  classical
  intro r
  have hS' : ∀ q ∈ Vf ×ˢ Lf, ∃ c : ℝ, ∀ x ∈ S,
      ‖q.2 (ρ x q.1)‖ ≤ c * Ξ x * (1 + σ x) ^ (-r) := fun q hq =>
    hS q.1 (Finset.mem_product.mp hq).1 q.2 (Finset.mem_product.mp hq).2 r
  choose! c hc using hS'
  refine ⟨∑ q ∈ Vf ×ˢ Lf, |c q|, fun n hn => ?_⟩
  obtain ⟨k₁, hk₁, x, hx, k₂, hk₂, rfl⟩ := hcartan n hn
  have hq : (ρ k₂ v, ℓ ∘ₗ ρ k₁) ∈ Vf ×ˢ Lf := Finset.mem_product.mpr ⟨hVf k₂ hk₂, hLf k₁ hk₁⟩
  have heq : ℓ (ρ (k₁ * x * k₂) v) = (ℓ ∘ₗ ρ k₁) (ρ x (ρ k₂ v)) := by
    simp only [map_mul, Module.End.mul_apply, LinearMap.coe_comp, Function.comp_apply]
  have hpos : 0 ≤ Ξ x * (1 + σ x) ^ (-r) :=
    mul_nonneg (hΞ0 x) (Real.rpow_nonneg (by linarith [hσ0 x]) _)
  have hterm : |c (ρ k₂ v, ℓ ∘ₗ ρ k₁)| ≤ ∑ q ∈ Vf ×ˢ Lf, |c q| :=
    Finset.single_le_sum (f := fun q => |c q|) (fun q _ => abs_nonneg _) hq
  rw [hΞK k₁ hk₁ k₂ hk₂, hσK k₁ hk₁ k₂ hk₂]
  change ‖ℓ (ρ (k₁ * x * k₂) v)‖ ≤ _
  rw [heq]
  calc ‖(ℓ ∘ₗ ρ k₁) (ρ x (ρ k₂ v))‖
      ≤ c (ρ k₂ v, ℓ ∘ₗ ρ k₁) * Ξ x * (1 + σ x) ^ (-r) := hc _ hq x hx
    _ = c (ρ k₂ v, ℓ ∘ₗ ρ k₁) * (Ξ x * (1 + σ x) ^ (-r)) := by ring
    _ ≤ (∑ q ∈ Vf ×ˢ Lf, |c q|) * (Ξ x * (1 + σ x) ^ (-r)) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans hterm) hpos
    _ = (∑ q ∈ Vf ×ˢ Lf, |c q|) * Ξ x * (1 + σ x) ^ (-r) := by ring

/-- **Corollary III.1.2 from exponential bounds on the chamber**: under the hypotheses of
`isRapidlyDecreasingOn_of_cartan` for `N`, `K`, `S`, `v`, `ℓ`, `Vf`, `Lf`, if `S` is covered by
finitely many sets `T i`, `1 + σ ≤ c (1 + ‖H‖)` on `S`, and every coefficient
`ℓ'(ρ(·) v')`, `v' ∈ Vf`, `ℓ' ∈ Lf`, is bounded on each `T i` by `C Ξ e^{−ε ‖H‖}` for some
`ε > 0`, then `g ↦ ℓ(ρ(g) v)` decreases rapidly on `N`. -/
theorem isRapidlyDecreasingOn_of_cartan_of_exp (ρ : Representation ℂ G V) {Ξ σ : G → ℝ}
    (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g) {N K : Subgroup G} {S : Set G}
    (hcartan : ∀ n ∈ N, ∃ k₁ ∈ K, ∃ x ∈ S, ∃ k₂ ∈ K, n = k₁ * x * k₂)
    (hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g)
    (hσK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, σ (k₁ * g * k₂) = σ g) (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (Vf : Finset V) (Lf : Finset (V →ₗ[ℂ] ℂ)) (hVf : ∀ k ∈ K, ρ k v ∈ Vf)
    (hLf : ∀ k ∈ K, ℓ ∘ₗ ρ k ∈ Lf) {E : Type*} [SeminormedAddCommGroup E] {H : G → E}
    (hσH : ∃ c : ℝ, ∀ x ∈ S, 1 + σ x ≤ c * (1 + ‖H x‖)) {ι : Type*} (s : Finset ι)
    (T : ι → Set G) (hcover : S ⊆ ⋃ i ∈ s, T i)
    (hexp : ∀ v' ∈ Vf, ∀ ℓ' ∈ Lf, ∀ i ∈ s,
      IsExpDecreasingOn Ξ H (T i) fun x => ℓ' (ρ x v')) :
    IsRapidlyDecreasingOn Ξ σ N (fun g => ℓ (ρ g v)) :=
  isRapidlyDecreasingOn_of_cartan ρ hΞ0 hσ0 hcartan hΞK hσK v ℓ Vf Lf hVf hLf
    fun v' hv' ℓ' hℓ' r => exists_rpow_bound_of_exp_bound (fun x _ => hΞ0 x)
      (fun x _ => hσ0 x) hσH s T hcover (hexp v' hv' ℓ' hℓ') r

end Cartan

end Langlands.HarishChandraSchwartz
