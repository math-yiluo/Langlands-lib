import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Langlands.Representation.Plancherel.CoefficientTensors

/-! # Coefficients cut off by `C_c(G/G¹)` lie in `C(G)` (III.7)

Waldspurger III.7: for a square integrable admissible representation `ω`, `f ∈ A(ω)` and
`ϕ ∈ C_c(G/G¹)`, the product `f ϕ` lies in `C(G)`, by Corollary III.1.2. Here `G¹` is an
arbitrary open normal subgroup `N`, `A(ω)` is the range of the published coefficient map
`Plancherel.coefficientTensorMap`, the conclusion of Corollary III.1.2 (rapid decay of the
coefficients on `N`) is the hypothesis `HasRapidlyDecreasingCoefficientsOn`, and the
translation bounds of the weights are the hypothesis `TranslationWeights`.
-/

noncomputable section

universe u v

open scoped ENNReal

namespace Langlands.HarishChandraSchwartz

section Cutoff

variable {G : Type u} [Group G] {Ξ σ : G → ℝ}

/-- `f` decreases rapidly on the subgroup `N`: for every `r` there is `c` with
`|f(n)| ≤ c Ξ(n) (1 + σ(n))^{-r}` for all `n ∈ N` (the bound of Corollary III.1.2, where
`N = G¹`). -/
def IsRapidlyDecreasingOn (Ξ σ : G → ℝ) (N : Subgroup G) (f : G → ℂ) : Prop :=
  ∀ r : ℝ, ∃ c : ℝ, ∀ n ∈ N, ‖f n‖ ≤ c * Ξ n * (1 + σ n) ^ (-r)

/-- Rapid decay on `N` is stable under addition. -/
theorem IsRapidlyDecreasingOn.add {N : Subgroup G} {f₁ f₂ : G → ℂ}
    (h₁ : IsRapidlyDecreasingOn Ξ σ N f₁) (h₂ : IsRapidlyDecreasingOn Ξ σ N f₂) :
    IsRapidlyDecreasingOn Ξ σ N (f₁ + f₂) := by
  intro r
  obtain ⟨c₁, hc₁⟩ := h₁ r
  obtain ⟨c₂, hc₂⟩ := h₂ r
  refine ⟨c₁ + c₂, fun n hn => ?_⟩
  calc ‖(f₁ + f₂) n‖ ≤ ‖f₁ n‖ + ‖f₂ n‖ := norm_add_le _ _
    _ ≤ c₁ * Ξ n * (1 + σ n) ^ (-r) + c₂ * Ξ n * (1 + σ n) ^ (-r) :=
        add_le_add (hc₁ n hn) (hc₂ n hn)
    _ = (c₁ + c₂) * Ξ n * (1 + σ n) ^ (-r) := by ring

omit [Group G] in
/-- A pointwise bound `|f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` gives `ν_r(f) < ∞`. -/
theorem nu_ne_top_of_norm_le (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) {f : G → ℂ} {c r : ℝ}
    (h : ∀ g, ‖f g‖ ≤ c * Ξ g * (1 + σ g) ^ (-r)) : nu Ξ σ r f ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := c)) (iSup_le fun g => ?_)
  have hb : 0 < 1 + σ g := by linarith [hσ g]
  rw [weight, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hw : 0 ≤ (Ξ g)⁻¹ * (1 + σ g) ^ r :=
    mul_nonneg (inv_nonneg.mpr (hΞ g).le) (Real.rpow_nonneg hb.le _)
  calc ‖f g‖ * ((Ξ g)⁻¹ * (1 + σ g) ^ r)
      ≤ c * Ξ g * (1 + σ g) ^ (-r) * ((Ξ g)⁻¹ * (1 + σ g) ^ r) :=
        mul_le_mul_of_nonneg_right (h g) hw
    _ = c * (Ξ g * (Ξ g)⁻¹) * ((1 + σ g) ^ (-r) * (1 + σ g) ^ r) := by ring
    _ = c := by
        rw [mul_inv_cancel₀ (hΞ g).ne', ← Real.rpow_add hb, neg_add_cancel, Real.rpow_zero]
        ring

/-- If the left translate `f(g₀ ·)` decreases rapidly on `N`, then `f` decreases rapidly on
the coset `g₀ N`, measured at the point itself: for every `r` there is `c` with
`|f(g)| ≤ c Ξ(g) (1 + σ(g))^{-r}` whenever `g₀⁻¹ g ∈ N`. -/
theorem TranslationWeights.exists_norm_le_of_mem_coset (ht : TranslationWeights Ξ σ)
    {N : Subgroup G} {f : G → ℂ} {g₀ : G}
    (hf : IsRapidlyDecreasingOn Ξ σ N (fun x => f (g₀ * x))) (r : ℝ) :
    ∃ c : ℝ, ∀ g, g₀⁻¹ * g ∈ N → ‖f g‖ ≤ c * Ξ g * (1 + σ g) ^ (-r) := by
  obtain ⟨d, hd⟩ := ht.bound
  obtain ⟨C₁, hC₁⟩ := hd g₀⁻¹ 1
  obtain ⟨C₂, hC₂⟩ := ht.heightBound g₀ 1
  set s : ℝ := max r 0 + d with hs_def
  have hs : 0 ≤ s := add_nonneg (le_max_right r 0) (Nat.cast_nonneg d)
  obtain ⟨c, hc⟩ := hf s
  have hpos : ∀ g, 0 < 1 + σ g := fun g => by linarith [ht.nonneg g]
  have hc0 : 0 ≤ c := by
    have h₁ := (norm_nonneg _).trans (hc 1 N.one_mem)
    rw [mul_assoc] at h₁
    exact (mul_nonneg_iff_of_pos_right
      (mul_pos (ht.pos 1) (Real.rpow_pos_of_pos (hpos 1) _))).mp h₁
  have hC₁0 : 0 ≤ C₁ := by
    have h₁ := (ht.pos _).trans_le (hC₁ 1)
    rw [mul_assoc] at h₁
    exact ((mul_pos_iff_of_pos_right (mul_pos (ht.pos 1) (pow_pos (hpos 1) d))).mp h₁).le
  have hC₂0 : 0 < C₂ :=
    (mul_pos_iff_of_pos_right (hpos 1)).mp ((hpos _).trans_le (hC₂ 1))
  refine ⟨c * C₁ * C₂ ^ s, fun g hg => ?_⟩
  set n := g₀⁻¹ * g with hn_def
  have hgn : g₀ * n = g := by rw [hn_def, mul_inv_cancel_left]
  have hfn : ‖f g‖ ≤ c * Ξ n * (1 + σ n) ^ (-s) := by
    simpa only [hgn] using hc n hg
  have hΞn : Ξ n ≤ C₁ * Ξ g * (1 + σ g) ^ d := by
    have := hC₁ g
    rwa [mul_one] at this
  have hσn : 1 + σ g ≤ C₂ * (1 + σ n) := by
    have := hC₂ n
    rwa [mul_one, hgn] at this
  have hrp : (1 + σ n) ^ (-s) ≤ C₂ ^ s * (1 + σ g) ^ (-s) := by
    have hx := Real.rpow_pos_of_pos (hpos n) s
    have hy := Real.rpow_pos_of_pos (hpos g) s
    rw [Real.rpow_neg (hpos n).le, Real.rpow_neg (hpos g).le, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ hx hy, one_mul, ← Real.mul_rpow hC₂0.le (hpos n).le]
    exact Real.rpow_le_rpow (hpos g).le hσn hs
  have hexp : (1 + σ g) ^ d * (1 + σ g) ^ (-s) ≤ (1 + σ g) ^ (-r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (hpos g)]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [ht.nonneg g]) ?_
    rw [hs_def]
    linarith [le_max_left r 0]
  calc ‖f g‖ ≤ c * Ξ n * (1 + σ n) ^ (-s) := hfn
    _ ≤ c * (C₁ * Ξ g * (1 + σ g) ^ d) * (C₂ ^ s * (1 + σ g) ^ (-s)) := by
        gcongr
        · exact Real.rpow_nonneg (hpos n).le _
        · exact mul_nonneg hc0
            (mul_nonneg (mul_nonneg hC₁0 (ht.pos g).le) (pow_nonneg (hpos g).le d))
    _ = c * C₁ * C₂ ^ s * Ξ g * ((1 + σ g) ^ d * (1 + σ g) ^ (-s)) := by ring
    _ ≤ c * C₁ * C₂ ^ s * Ξ g * (1 + σ g) ^ (-r) := by
        gcongr
        exact mul_nonneg (mul_nonneg (mul_nonneg hc0 hC₁0)
          (Real.rpow_nonneg hC₂0.le _)) (ht.pos g).le

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The product of a function bi-invariant under `H ≤ N` with a function on `G/N`
(`N` normal) is bi-invariant under `H`. -/
theorem IsBiInvariant.mul_quotient {N : Subgroup G} [N.Normal] {H : Subgroup G} (hHN : H ≤ N)
    {f : G → ℂ} (hf : IsBiInvariant H f) (φ : G ⧸ N → ℂ) :
    IsBiInvariant H (fun g => f g * φ g) := by
  intro h₁ h₁m h₂ h₂m g
  have hq : ((h₁ * g * h₂ : G) : G ⧸ N) = (g : G ⧸ N) := by
    rw [QuotientGroup.eq]
    have h₃ : (h₁ * g * h₂)⁻¹ * g = h₂⁻¹ * (g⁻¹ * h₁⁻¹ * g⁻¹⁻¹) := by group
    rw [h₃]
    exact N.mul_mem (N.inv_mem (hHN h₂m))
      (Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem (hHN h₁m)) g⁻¹)
  simp only [hf h₁ h₁m h₂ h₂m g, hq]

/-- Waldspurger III.7 (the analytic part): let `N` be an open normal subgroup, `f` bi-invariant
under a subgroup `H ≤ N` such that every left translate `f(g₀ ·)` decreases rapidly on `N`,
and `φ` a compactly supported function on the discrete group `G/N`. Then `f φ` lies in the
level `C_H`. -/
theorem TranslationWeights.mul_mem_levelSubmodule (ht : TranslationWeights Ξ σ)
    {N : Subgroup G} [N.Normal] (hN : IsOpen (N : Set G)) {H : Subgroup G} (hHN : H ≤ N)
    {f : G → ℂ} (hf : IsBiInvariant H f)
    (hdec : ∀ g₀ : G, IsRapidlyDecreasingOn Ξ σ N (fun x => f (g₀ * x)))
    {φ : G ⧸ N → ℂ} (hφ : HasCompactSupport φ) :
    (fun g => f g * φ g) ∈ levelSubmodule Ξ σ H := by
  refine ⟨hf.mul_quotient hHN φ, fun r => lt_top_iff_ne_top.mpr ?_⟩
  have := QuotientGroup.discreteTopology hN
  have hfin : (Function.support φ).Finite :=
    hφ.isCompact.finite_of_discrete.subset (subset_tsupport φ)
  choose c hc using fun q : G ⧸ N =>
    ht.exists_norm_le_of_mem_coset (hdec (Quotient.out q)) r
  refine nu_ne_top_of_norm_le ht.pos ht.nonneg
    (c := ∑ q ∈ hfin.toFinset, |c q| * ‖φ q‖) fun g => ?_
  have hW : 0 ≤ Ξ g * (1 + σ g) ^ (-r) :=
    mul_nonneg (ht.pos g).le (Real.rpow_nonneg (by linarith [ht.nonneg g]) _)
  by_cases hg : φ (g : G ⧸ N) = 0
  · simp only [hg, mul_zero, norm_zero, mul_assoc]
    exact mul_nonneg (Finset.sum_nonneg fun q _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)) hW
  · set q : G ⧸ N := (g : G ⧸ N) with hq_def
    have hmem : (Quotient.out q)⁻¹ * g ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have hqS : q ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hg
    calc ‖f g * φ q‖ = ‖f g‖ * ‖φ q‖ := norm_mul _ _
      _ ≤ (c q * Ξ g * (1 + σ g) ^ (-r)) * ‖φ q‖ :=
          mul_le_mul_of_nonneg_right (hc q g hmem) (norm_nonneg _)
      _ ≤ (|c q| * ‖φ q‖) * (Ξ g * (1 + σ g) ^ (-r)) := by
          rw [mul_assoc (c q), mul_comm _ ‖φ q‖, mul_comm (|c q|) ‖φ q‖, mul_assoc ‖φ q‖]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hW)
            (norm_nonneg _)
      _ ≤ (∑ q ∈ hfin.toFinset, |c q| * ‖φ q‖) * (Ξ g * (1 + σ g) ^ (-r)) :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun q => |c q| * ‖φ q‖)
            (fun q _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)) hqS) hW
      _ = (∑ q ∈ hfin.toFinset, |c q| * ‖φ q‖) * Ξ g * (1 + σ g) ^ (-r) := by ring

end Cutoff

section Coefficients

open Plancherel (CoefficientTensor coefficientTensorMap coefficientTensorAction
  coefficientTensorMap_tmul coefficientTensorMap_action coefficientTensorMap_biInvariant)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}

/-- The conclusion of Waldspurger's Corollary III.1.2 for `ρ` on the subgroup `N` (`N = G¹`):
every coefficient `g ↦ ℓ(ρ(g) v)`, `v ∈ V`, `ℓ` a smooth functional, decreases rapidly
on `N`. -/
def HasRapidlyDecreasingCoefficientsOn {V : Type v} [AddCommGroup V] [Module ℂ V]
    (Ξ σ : G → ℝ) (N : Subgroup G) (ρ : Representation ℂ G V) : Prop :=
  ∀ (v : V) (ℓ : SmoothDual ρ), IsRapidlyDecreasingOn Ξ σ N (fun g => ℓ.val (ρ g v))

variable {A : SmoothRep.{0, u, v} ℂ G} {N : Subgroup G}

/-- Rapid decay on `N` of the pure coefficients passes to every element of `A(π)`, the image
of the coefficient map. -/
theorem isRapidlyDecreasingOn_coefficientTensorMap
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation) (t : CoefficientTensor A) :
    IsRapidlyDecreasingOn Ξ σ N ⇑(coefficientTensorMap A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    have h : ⇑(coefficientTensorMap A (v ⊗ₜ[ℂ] ℓ)) = fun g => ℓ.val (A.representation g v) :=
      funext fun g => coefficientTensorMap_tmul A v ℓ g
    rw [h]
    exact hD v ℓ
  | add t s ht hs => simpa only [map_add, LocallyConstant.coe_add] using ht.add hs

/-- Every left translate of an element of `A(π)` decreases rapidly on `N`. -/
theorem isRapidlyDecreasingOn_coefficientTensorMap_mul_left
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation) (t : CoefficientTensor A)
    (g₀ : G) : IsRapidlyDecreasingOn Ξ σ N (fun x => coefficientTensorMap A t (g₀ * x)) := by
  have h : (fun x => coefficientTensorMap A t (g₀ * x)) =
      ⇑(coefficientTensorMap A (coefficientTensorAction A (1, g₀⁻¹) t)) := by
    funext x
    rw [coefficientTensorMap_action]
    simp
  rw [h]
  exact isRapidlyDecreasingOn_coefficientTensorMap hD _

/-- Waldspurger III.7 for one coefficient tensor: if the coefficients of the smooth
representation `A` decrease rapidly on the open normal subgroup `N` (the conclusion of
Corollary III.1.2 for a square integrable `A` and `N = G¹`), then `f φ ∈ C(G)` for the
coefficient `f` of every `t ∈ A ⊗ Ã` and every compactly supported `φ` on `G/N`. -/
theorem TranslationWeights.coefficientTensorMap_mul_mem_schwartzSubmodule
    [Nonempty (CompactOpenSubgroup G)] (ht : TranslationWeights Ξ σ) [N.Normal]
    (hN : IsOpen (N : Set G)) (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation)
    (t : CoefficientTensor A) {φ : G ⧸ N → ℂ} (hφ : HasCompactSupport φ) :
    (fun g => coefficientTensorMap A t g * φ g) ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨U, hU⟩ := coefficientTensorMap_biInvariant A t
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (CompactOpenSubgroup G))
  let W : OpenSubgroup G := K₀.1 ⊓ U ⊓ ⟨N, hN⟩
  have hWc : IsCompact (W : Set G) := by
    have : (W : Set G) = (K₀.1 : Set G) ∩ ((U ⊓ ⟨N, hN⟩ : OpenSubgroup G) : Set G) := by
      simp only [W, OpenSubgroup.coe_inf, Set.inter_assoc]
    rw [this]
    exact K₀.2.inter_right (U ⊓ ⟨N, hN⟩).isClosed
  let H : CompactOpenSubgroup G := ⟨W, hWc⟩
  have hHN : H.toSubgroup ≤ N := fun x hx => hx.2
  have hf : IsBiInvariant H.toSubgroup ⇑(coefficientTensorMap A t) :=
    fun h₁ h₁m h₂ h₂m g => hU ⟨h₁, h₁m.1.2⟩ ⟨h₂, h₂m.1.2⟩ g
  exact levelSubmodule_le_schwartzSubmodule Ξ σ H (ht.mul_mem_levelSubmodule hN hHN hf
    (isRapidlyDecreasingOn_coefficientTensorMap_mul_left hD t) hφ)

/-- Waldspurger III.7: if the coefficients of the smooth representation `A` decrease rapidly
on the open normal subgroup `N` (the conclusion of Corollary III.1.2 for a square integrable
`A` and `N = G¹`), then `f φ ∈ C(G)` for every `f ∈ A(π)` (the range of the coefficient map)
and every compactly supported `φ` on `G/N`. -/
theorem TranslationWeights.mul_mem_schwartzSubmodule [Nonempty (CompactOpenSubgroup G)]
    (ht : TranslationWeights Ξ σ) [N.Normal] (hN : IsOpen (N : Set G))
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation) {f : LocallyConstant G ℂ}
    (hf : f ∈ LinearMap.range (coefficientTensorMap A)) {φ : G ⧸ N → ℂ}
    (hφ : HasCompactSupport φ) :
    (fun g => f g * φ g) ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨t, rfl⟩ := hf
  exact ht.coefficientTensorMap_mul_mem_schwartzSubmodule hN hD t hφ

end Coefficients

end Langlands.HarishChandraSchwartz
