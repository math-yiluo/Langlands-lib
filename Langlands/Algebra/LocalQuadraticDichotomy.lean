import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# A ramification dichotomy for quadratic extensions of local fields

Let `L/K` be a quadratic extension of nonarchimedean local fields with nontrivial
automorphism `σ`. If some element of `K` does not have the valuation of a square of an element
of `L` (so `L/K` is unramified), then some integral element `θ` of `L` satisfies
`|σ θ - θ| = 1`, i.e. `σ` acts nontrivially on the residue field of `L`.
-/

noncomputable section

namespace Langlands.LocalQuadratic

universe u v

open ValuativeRel WithZero

section Log

variable (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- The integer-valued logarithm of the discrete valuation. -/
def vlog (x : L) : ℤ :=
  WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L (valuation L x))

variable {L}

theorem iso_ne_zero {x : L} (hx : x ≠ 0) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L (valuation L x) ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).symm h
  rw [OrderMonoidIso.symm_apply_apply, map_zero] at h'
  exact (valuation L).zero_iff.mp h'

theorem vlog_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : vlog L (x * y) = vlog L x + vlog L y := by
  rw [vlog, map_mul, map_mul, log_mul (iso_ne_zero hx) (iso_ne_zero hy)]
  rfl

theorem vlog_le_iff {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    vlog L x ≤ vlog L y ↔ valuation L x ≤ valuation L y := by
  rw [vlog, vlog, log_le_log (iso_ne_zero hx) (iso_ne_zero hy)]
  exact map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)

theorem vlog_eq_iff {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    vlog L x = vlog L y ↔ valuation L x = valuation L y := by
  rw [le_antisymm_iff, le_antisymm_iff, vlog_le_iff hx hy, vlog_le_iff hy hx]

theorem exists_vlog_eq (n : ℤ) : ∃ x : L, x ≠ 0 ∧ vlog L x = n := by
  obtain ⟨x, hx⟩ := valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).symm (exp n))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    have := congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L) hx
    rw [map_zero, OrderMonoidIso.apply_symm_apply] at this
    exact exp_ne_zero this.symm
  refine ⟨x, hx0, ?_⟩
  rw [vlog, hx, OrderMonoidIso.apply_symm_apply, log_exp]

end Log

section Dichotomy

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] {σ : L →+* L}
  (hσ : ∀ c, valuation L (σ c) = valuation L c)
  (hσK : ∀ k : K, σ (algebraMap K L k) = algebraMap K L k)
  (hσσ : ∀ c, σ (σ c) = c)
  (hfix : ∀ ℓ : L, σ ℓ = ℓ → ∃ k : K, algebraMap K L k = ℓ)
  (hKL : ∀ a b : K, valuation L (algebraMap K L a) ≤ valuation L (algebraMap K L b) ↔
    valuation K a ≤ valuation K b)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
include hσ hσσ hfix in
/-- If some element of `K` does not have a square valuation in `L`, every valuation of `L` is
the valuation of an element of `K`. -/
theorem exists_base_of_not_squares
    (hnsq : ∃ c : K, c ≠ 0 ∧ ∀ ℓ : L, ℓ ≠ 0 →
      valuation L (algebraMap K L c) ≠ valuation L ℓ ^ 2)
    (x : L) (hx : x ≠ 0) : ∃ k : K, k ≠ 0 ∧ valuation L (algebraMap K L k) = valuation L x := by
  obtain ⟨c₀, hc₀, hc₀sq⟩ := hnsq
  have hvlogσ : ∀ y : L, vlog L (σ y) = vlog L y := fun y => by rw [vlog, vlog, hσ]
  have hσne : ∀ y : L, y ≠ 0 → σ y ≠ 0 := fun y hy h => by
    have := hσ y
    rw [h, map_zero] at this
    exact hy ((valuation L).zero_iff.mp this.symm)
  have hnorm : ∀ y : L, y ≠ 0 → ∃ k : K, k ≠ 0 ∧ algebraMap K L k = y * σ y := by
    intro y hy
    obtain ⟨k, hk⟩ := hfix (y * σ y) (by rw [map_mul, hσσ, mul_comm])
    refine ⟨k, fun h => ?_, hk⟩
    rw [h, map_zero] at hk
    exact mul_ne_zero hy (hσne y hy) hk.symm
  have hc₀L : algebraMap K L c₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hc₀
  have hodd : ¬ Even (vlog L (algebraMap K L c₀)) := by
    rintro ⟨m, hm⟩
    obtain ⟨ℓ, hℓ, hℓm⟩ := exists_vlog_eq (L := L) m
    apply hc₀sq ℓ hℓ
    rw [← map_pow, ← vlog_eq_iff hc₀L (pow_ne_zero 2 hℓ), hm, pow_two, vlog_mul hℓ hℓ, hℓm]
  rcases Int.even_or_odd (vlog L x) with ⟨m, hm⟩ | hxodd
  · obtain ⟨y, hy, hym⟩ := exists_vlog_eq (L := L) m
    obtain ⟨k, hk, hky⟩ := hnorm y hy
    refine ⟨k, hk, ?_⟩
    rw [← vlog_eq_iff ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hk) hx, hky,
      vlog_mul hy (hσne y hy), hvlogσ, hym, hm]
  · have heven : Even (vlog L x - vlog L (algebraMap K L c₀)) :=
      Odd.sub_odd hxodd (Int.not_even_iff_odd.mp hodd)
    obtain ⟨m, hm⟩ := heven
    obtain ⟨y, hy, hym⟩ := exists_vlog_eq (L := L) m
    obtain ⟨k, hk, hky⟩ := hnorm y hy
    refine ⟨c₀ * k, mul_ne_zero hc₀ hk, ?_⟩
    have hkL : algebraMap K L k ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hk
    have hprod : algebraMap K L (c₀ * k) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hc₀L hkL
    rw [← vlog_eq_iff hprod hx, map_mul, vlog_mul hc₀L hkL, hky, vlog_mul hy (hσne y hy),
      hvlogσ, hym]
    linarith

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
include hσ hσσ hfix hKL in
/-- A unit of `L` fixed by `σ` modulo the maximal ideal is congruent to an element of `K`. -/
theorem exists_base_approx (u : L) (hu : valuation L u = 1)
    (hσu : valuation L (σ u - u) < 1) :
    ∃ r : K, valuation K r ≤ 1 ∧ valuation L (u - algebraMap K L r) < 1 := by
  have hσu1 : valuation L (σ u) = 1 := by rw [hσ, hu]
  obtain ⟨t, ht⟩ := hfix (u + σ u) (by rw [map_add, hσσ, add_comm])
  obtain ⟨n, hn⟩ := hfix (u * σ u) (by rw [map_mul, hσσ, mul_comm])
  have hle1 : ∀ a : K, valuation L (algebraMap K L a) ≤ 1 ↔ valuation K a ≤ 1 := fun a => by
    simpa using hKL a 1
  have hlt1 : ∀ a : K, valuation L (algebraMap K L a) < 1 ↔ valuation K a < 1 := fun a => by
    have h := hKL 1 a
    simp only [map_one] at h
    rw [← not_le, ← not_le, h]
  have h2le : valuation L (2 : L) ≤ 1 := by
    rw [show (2 : L) = 1 + 1 by norm_num]
    exact ((valuation L).map_add 1 1).trans (by simp)
  have hsub_symm : valuation L (u - σ u) = valuation L (σ u - u) := by
    rw [← Valuation.map_neg, neg_sub]
  rcases h2le.lt_or_eq with h2 | h2
  · -- residue characteristic two
    have h2K : valuation K (2 : K) < 1 := by
      rw [← hlt1, map_ofNat]
      exact h2
    have hint := Valuation.integer.integers (valuation K)
    have hres2 : (2 : 𝓀[K]) = 0 := by
      have h : IsLocalRing.residue 𝒪[K] (2 : 𝒪[K]) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          hint.isUnit_iff_valuation_eq_one]
        exact h2K.ne
      rwa [map_ofNat] at h
    have hinj : Function.Injective (fun x : 𝓀[K] => x ^ 2) := by
      intro x y hxy
      simp only at hxy
      have h0 : (x - y) ^ 2 = 0 := by
        have e : (x - y) ^ 2 = (x ^ 2 - y ^ 2) - 2 * y * (x - y) := by ring
        rw [e, hxy, sub_self, hres2, zero_mul, zero_mul, sub_zero]
      exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
    have hsurj := Finite.injective_iff_surjective.mp hinj
    have hn1 : valuation K n ≤ 1 := by
      rw [← hle1, hn, map_mul, hu, hσu1, one_mul]
    let n₀ : 𝒪[K] := ⟨n, hn1⟩
    obtain ⟨sb, hsb⟩ := hsurj (IsLocalRing.residue 𝒪[K] n₀)
    obtain ⟨s₀, hs₀⟩ := IsLocalRing.residue_surjective sb
    have hsn : valuation K ((s₀ : K) ^ 2 - n) < 1 := by
      have h : IsLocalRing.residue 𝒪[K] (s₀ ^ 2 - n₀) = 0 := by
        rw [map_sub, map_pow, hs₀]
        exact sub_eq_zero.mpr hsb
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        hint.isUnit_iff_valuation_eq_one] at h
      have hcoe : ((s₀ ^ 2 - n₀ : 𝒪[K]) : K) = (s₀ : K) ^ 2 - n := by
        push_cast
        rfl
      have hle : valuation K ((s₀ ^ 2 - n₀ : 𝒪[K]) : K) ≤ 1 := (s₀ ^ 2 - n₀).prop
      have h' : ¬ valuation K ((s₀ ^ 2 - n₀ : 𝒪[K]) : K) = 1 := h
      rw [hcoe] at hle h'
      exact lt_of_le_of_ne hle h'
    refine ⟨s₀, s₀.prop, ?_⟩
    have hr1 : valuation L (algebraMap K L (s₀ : K)) ≤ 1 := (hle1 _).mpr s₀.prop
    have hT : valuation L (u + σ u - 2 * algebraMap K L (s₀ : K)) < 1 := by
      have e : u + σ u - 2 * algebraMap K L (s₀ : K) =
          2 * u + (σ u - u) - 2 * algebraMap K L (s₀ : K) := by ring
      rw [e]
      refine (valuation L).map_sub_lt ((valuation L).map_add_lt ?_ hσu) ?_
      · rw [map_mul, hu, mul_one]
        exact h2
      · rw [map_mul]
        exact (mul_le_of_le_one_right zero_le hr1).trans_lt h2
    have hN : valuation L (algebraMap K L (s₀ : K) ^ 2 - u * σ u) < 1 := by
      rw [← hn, ← map_pow, ← map_sub, hlt1]
      exact hsn
    have hsq : (u - algebraMap K L (s₀ : K)) ^ 2 =
        (u + σ u - 2 * algebraMap K L (s₀ : K)) * u +
          (algebraMap K L (s₀ : K) ^ 2 - u * σ u) := by ring
    have h' : valuation L ((u - algebraMap K L (s₀ : K)) ^ 2) < 1 := by
      rw [hsq]
      refine (valuation L).map_add_lt ?_ hN
      rw [map_mul, hu, mul_one]
      exact hT
    rw [map_pow] at h'
    exact (pow_lt_one_iff_of_nonneg zero_le (by norm_num)).mp h'
  · -- the residue characteristic is not two
    have h2L : (2 : L) ≠ 0 := fun h => by
      rw [h, map_zero] at h2
      exact zero_ne_one h2
    have h2K : (2 : K) ≠ 0 := fun h => by
      apply h2L
      have := congrArg (algebraMap K L) h
      rwa [map_ofNat, map_zero] at this
    refine ⟨t / 2, ?_, ?_⟩
    · rw [← hle1, map_div₀, ht, map_ofNat, map_div₀, h2, div_one]
      exact ((valuation L).map_add u (σ u)).trans (by rw [hu, hσu1, max_self])
    · have e : u - algebraMap K L (t / 2) = (u - σ u) / 2 := by
        rw [map_div₀, ht, map_ofNat]
        field_simp
        ring
      rw [e, map_div₀, h2, div_one, hsub_symm]
      exact hσu

include hσ hσK hσσ hfix hKL in
/-- If every valuation of `L` is attained on `K`, every element of `L` outside `K` is
approximated by `K` up to `|σ y - y|`. -/
theorem exists_close_base
    (hall : ∀ x : L, x ≠ 0 → ∃ k : K, k ≠ 0 ∧ valuation L (algebraMap K L k) = valuation L x) :
    ∀ (m : ℕ) (y : L), σ y ≠ y → vlog L y - vlog L (σ y - y) ≤ m →
      ∃ k : K, valuation L (y - algebraMap K L k) ≤ valuation L (σ y - y) := by
  intro m
  induction m with
  | zero =>
    intro y hy hm
    have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hδ0 : σ y - y ≠ 0 := sub_ne_zero.mpr hy
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    exact (vlog_le_iff hy0 hδ0).mp (by omega)
  | succ m ih =>
    intro y hy hm
    have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hδ0 : σ y - y ≠ 0 := sub_ne_zero.mpr hy
    by_cases hle : valuation L y ≤ valuation L (σ y - y)
    · exact ⟨0, by rwa [map_zero, sub_zero]⟩
    push Not at hle
    obtain ⟨c, hc0, hc⟩ := hall y hy0
    have hcL0 : algebraMap K L c ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hc0
    have hvy : 0 < valuation L y := by
      rw [zero_lt_iff]
      exact (valuation L).ne_zero_iff.mpr hy0
    have hu : valuation L ((algebraMap K L c)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv₀, hc, inv_mul_cancel₀ hvy.ne']
    have hσu : σ ((algebraMap K L c)⁻¹ * y) - (algebraMap K L c)⁻¹ * y =
        (algebraMap K L c)⁻¹ * (σ y - y) := by
      rw [map_mul, map_inv₀, hσK, mul_sub]
    have hσu' : valuation L (σ ((algebraMap K L c)⁻¹ * y) - (algebraMap K L c)⁻¹ * y) < 1 := by
      rw [hσu, map_mul, map_inv₀, hc, inv_mul_lt_one₀ hvy]
      exact hle
    obtain ⟨r, -, hr⟩ := exists_base_approx hσ hσσ hfix hKL _ hu hσu'
    set y' := y - algebraMap K L (c * r) with hy'def
    have hy'δ : σ y' - y' = σ y - y := by
      rw [hy'def, map_sub, hσK]
      ring
    have hy' : σ y' ≠ y' := sub_ne_zero.mp (by rw [hy'δ]; exact hδ0)
    have hy'0 : y' ≠ 0 := fun h => hy' (by rw [h, map_zero])
    have hy'eq : y' = algebraMap K L c * ((algebraMap K L c)⁻¹ * y - algebraMap K L r) := by
      rw [hy'def, mul_sub, mul_inv_cancel_left₀ hcL0, map_mul]
    have hlt : valuation L y' < valuation L y := by
      rw [hy'eq, map_mul, hc]
      exact mul_lt_of_lt_one_right hvy hr
    have hvlog : vlog L y' < vlog L y := by
      rw [lt_iff_not_ge, vlog_le_iff hy0 hy'0]
      exact not_le.mpr hlt
    obtain ⟨k', hk'⟩ := ih y' hy' (by rw [hy'δ]; omega)
    refine ⟨c * r + k', ?_⟩
    have e : y - algebraMap K L (c * r + k') = y' - algebraMap K L k' := by
      rw [hy'def, map_add]
      ring
    rw [e, ← hy'δ]
    exact hk'

include hσ hσK hσσ hfix hKL in
/-- **Dichotomy.** If some element of `K` does not have the valuation of a square in `L`, then
`σ` moves some integral element of `L` by a unit. -/
theorem exists_moved_of_not_squares
    (hnsq : ∃ c : K, c ≠ 0 ∧ ∀ ℓ : L, ℓ ≠ 0 →
      valuation L (algebraMap K L c) ≠ valuation L ℓ ^ 2)
    (θ₀ : L) (hθ₀ : σ θ₀ ≠ θ₀) :
    ∃ θ : L, valuation L θ ≤ 1 ∧ valuation L (σ θ - θ) = 1 := by
  have hall := exists_base_of_not_squares hσ hσσ hfix hnsq
  have hδ0 : σ θ₀ - θ₀ ≠ 0 := sub_ne_zero.mpr hθ₀
  obtain ⟨k, hk⟩ := exists_close_base hσ hσK hσσ hfix hKL hall
    (vlog L θ₀ - vlog L (σ θ₀ - θ₀)).toNat θ₀ hθ₀ (Int.self_le_toNat _)
  obtain ⟨c, hc0, hc⟩ := hall _ hδ0
  have hvδ : 0 < valuation L (σ θ₀ - θ₀) := by
    rw [zero_lt_iff]
    exact (valuation L).ne_zero_iff.mpr hδ0
  have hδ' : σ (θ₀ - algebraMap K L k) - (θ₀ - algebraMap K L k) = σ θ₀ - θ₀ := by
    rw [map_sub, hσK]
    ring
  refine ⟨(algebraMap K L c)⁻¹ * (θ₀ - algebraMap K L k), ?_, ?_⟩
  · rw [map_mul, map_inv₀, hc, inv_mul_le_one₀ hvδ]
    exact hk
  · rw [map_mul, map_inv₀, hσK, ← mul_sub, hδ', map_mul, map_inv₀, hc,
      inv_mul_cancel₀ hvδ.ne']

end Dichotomy

end Langlands.LocalQuadratic
