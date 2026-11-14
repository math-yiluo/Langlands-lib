import Langlands.GroupScheme.Examples.SU3RootParametersTowerValuation
import Langlands.GroupScheme.Examples.SU3RootScaling
import Mathlib.Data.Int.LeastGreatest

/-! # Maximal depths in quadratic root-coordinate cosets -/

noncomputable section

universe u v w

open Algebra

namespace Langlands.GroupScheme.SU3Root

namespace Parameters

variable {L : Type w} [Field L] {c : RingInvolution L}

/-- A point with prescribed first coordinate, using a supplied trace-one scalar. -/
def liftOfTraceOne {t : L} (ht : t + c.bar t = 1) (x : L) : Parameters c :=
  scale x ⟨(1, t), by simpa using ht⟩

@[simp] theorem liftOfTraceOne_first {t : L} (ht : t + c.bar t = 1) (x : L) :
    (liftOfTraceOne ht x).first = x := by
  change x * 1 = x
  exact mul_one x

@[simp] theorem liftOfTraceOne_second {t : L} (ht : t + c.bar t = 1) (x : L) :
    (liftOfTraceOne ht x).second = x * c.bar x * t := rfl

/-- Dividing a noncentral second coordinate by the norm of the first produces trace one. -/
theorem second_div_norm_traceOne (p : Parameters c) (hp : p.first ≠ 0) :
    p.second / (p.first * c.bar p.first) +
      c.bar (p.second / (p.first * c.bar p.first)) = 1 := by
  have hn : p.first * c.bar p.first ≠ 0 :=
    mul_ne_zero hp ((map_ne_zero _).mpr hp)
  rw [map_div₀ c.bar, map_mul, c.bar_bar, mul_comm (c.bar p.first) p.first,
    ← add_div, p.equation, div_self hn]

/-- Trace-one maximality bounds every noncentral point with the same first coordinate. -/
theorem second_le_liftOfTraceOne
    (ω : AddValuation L (WithTop ℝ)) {t : L} (ht : t + c.bar t = 1)
    (hmax : ∀ y : L, y + c.bar y = 1 → ω y ≤ ω t)
    (p : Parameters c) (hp : p.first ≠ 0) :
    ω p.second ≤ ω (liftOfTraceOne ht p.first).second := by
  have hn : p.first * c.bar p.first ≠ 0 :=
    mul_ne_zero hp ((map_ne_zero _).mpr hp)
  calc
    ω p.second = ω (p.second / (p.first * c.bar p.first) *
        (p.first * c.bar p.first)) := by rw [div_mul_cancel₀ _ hn]
    _ = ω (p.second / (p.first * c.bar p.first)) +
        ω (p.first * c.bar p.first) := ω.map_mul _ _
    _ ≤ ω t + ω (p.first * c.bar p.first) :=
      add_le_add (hmax _ (p.second_div_norm_traceOne hp)) le_rfl
    _ = ω (liftOfTraceOne ht p.first).second := by
      simp only [liftOfTraceOne_second, AddValuation.map_mul]
      ac_rfl

private theorem halfTop_mono : Monotone halfTop := by
  intro a b hab
  cases b using WithTop.recTopCoe with
  | top => exact le_top
  | coe b =>
    obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top hab)
    simp only [halfTop_coe, WithTop.coe_le_coe] at *
    linarith

/-- A maximal trace-one scalar gives a representative of maximal root depth in each
nonzero first-coordinate coset. -/
theorem depthA_le_liftOfTraceOne
    (ω : AddValuation L (WithTop ℝ)) {t : L} (ht : t + c.bar t = 1)
    (hmax : ∀ y : L, y + c.bar y = 1 → ω y ≤ ω t)
    (p : Parameters c) (hp : p.first ≠ 0) :
    depthA ω p ≤ depthA ω (liftOfTraceOne ht p.first) :=
  halfTop_mono (second_le_liftOfTraceOne ω ht hmax p hp)

/-- The depth of the displayed lift is the first-coordinate value plus a fixed offset. -/
theorem depthA_liftOfTraceOne
    (ω : AddValuation L (WithTop ℝ))
    (hinv : ∀ y : L, ω (c.bar y) = ω y)
    {t : L} (ht : t + c.bar t = 1) (x : L) :
    depthA ω (liftOfTraceOne ht x) = ω x + halfTop (ω t) := by
  exact depthA_scale ω hinv x (⟨(1, t), by simpa using ht⟩ : Parameters c)

/-- The image of a root-filtration level on a nonzero first coordinate is determined
by its optimal depth. -/
theorem exists_first_eq_mem_filtration_iff
    (ω : AddValuation L (WithTop ℝ))
    (hinv : ∀ y : L, ω (c.bar y) = ω y)
    {t : L} (ht : t + c.bar t = 1)
    (hmax : ∀ y : L, y + c.bar y = 1 → ω y ≤ ω t)
    (r : ℝ) {x : L} (hx : x ≠ 0) :
    (∃ p : Parameters c, p.first = x ∧ p ∈ filtration ω hinv r) ↔
      (r : WithTop ℝ) ≤ ω x + halfTop (ω t) := by
  constructor
  · rintro ⟨p, hpx, hpr⟩
    have h := depthA_le_liftOfTraceOne ω ht hmax p (by rwa [hpx])
    rw [hpx, depthA_liftOfTraceOne ω hinv] at h
    exact ((mem_filtration_iff_depth ω hinv r p).mp hpr).trans h
  · intro h
    refine ⟨liftOfTraceOne ht x, liftOfTraceOne_first ht x, ?_⟩
    rw [mem_filtration_iff_depth, depthA_liftOfTraceOne ω hinv]
    exact h

/-- Changing to the optimal representative is multiplication by an actual central point. -/
theorem exists_central_mul_eq_liftOfTraceOne
    {t : L} (ht : t + c.bar t = 1) (p : Parameters c) :
    ∃ z : central c, p * z.val = liftOfTraceOne ht p.first := by
  refine ⟨⟨p⁻¹ * liftOfTraceOne ht p.first, ?_⟩, ?_⟩
  · simp only [mem_central, first_mul, first_inv, liftOfTraceOne_first, neg_add_cancel]
  · simp only [mul_inv_cancel_left]

end Parameters

section Henselian

variable (k : Type u) (E : Type v) (L : Type w)
  [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
  [IsQuadraticExtension E L] [Algebra.IsSeparable E L] [Algebra.IsSeparable k L]
  [FiniteDimensional k E]
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

local instance : FiniteDimensional E L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two E L]; decide)

/-- Trace-one values have a maximum for the actual base-normalized henselian valuation. -/
theorem exists_maximal_tower_traceOne :
    ∃ t : L, t + (fieldInvolution E L).bar t = 1 ∧
      ∀ y : L, y + (fieldInvolution E L).bar y = 1 →
        FieldTheory.henselianSeparableAddValuation v hH L y ≤
          FieldTheory.henselianSeparableAddValuation v hH L t := by
  let ω := FieldTheory.henselianSeparableAddValuation v hH L
  let N : ℕ := Module.finrank k L
  let : FiniteDimensional k L := FiniteDimensional.trans k E L
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Module.finrank_pos (R := k) (M := L)
  have hnonzero : ∀ y : L, y + (fieldInvolution E L).bar y = 1 → y ≠ 0 := by
    intro y hy h
    exact zero_ne_one (by simpa only [h, map_zero, zero_add] using hy)
  have hbound : ∀ y : L, y + (fieldInvolution E L).bar y = 1 → ω y ≤ 0 := by
    intro y hy
    have h := ω.map_add y ((fieldInvolution E L).bar y)
    rw [henselianSeparableAddValuation_quadratic_bar k E L v hH,
      min_self, hy, ω.map_one] at h
    exact h
  obtain ⟨n, ⟨t, ht, hval⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ => ∃ t : L, t + (fieldInvolution E L).bar t = 1 ∧
      ω t = (((n : ℝ) / N : ℝ) : WithTop ℝ))
    ⟨0, by
      rintro n ⟨t, ht, hval⟩
      have h := hbound t ht
      rw [hval, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
      have hn : (n : ℝ) ≤ 0 := by simpa using (div_le_iff₀ hN).mp h
      exact_mod_cast hn⟩
    (by
      have ht := traceOne_add_conjugate E L
      obtain ⟨n, hn⟩ := FieldTheory.henselianSeparableAddValuation_exists_lattice_value
        v hH L (hnonzero _ ht)
      exact ⟨n, traceOne E L, ht, hn⟩)
  refine ⟨t, ht, fun y hy => ?_⟩
  obtain ⟨m, hm⟩ := FieldTheory.henselianSeparableAddValuation_exists_lattice_value
    v hH L (hnonzero y hy)
  change ω y ≤ ω t
  rw [hm, hval, WithTop.coe_le_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmax m ⟨y, hy, hm⟩) hN.le

end Henselian

end Langlands.GroupScheme.SU3Root
