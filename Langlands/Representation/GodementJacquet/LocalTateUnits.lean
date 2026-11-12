import Langlands.Representation.GodementJacquet.LocalTateFourier
import Langlands.Representation.Conductor.JacquetScaledLevel

/-! # Principal-unit levels, the unit Haar comparison and Gauss sums -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor RankinSelberg
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

section Invariance

/-- If left translation by `w` preserves a measurable set `S` and multiplies `f` by
`c ≠ 1`, then the integral of `f` over `S` against a left-invariant measure vanishes. -/
theorem setIntegral_eq_zero_of_mul_left {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {S : Set G}
    (hS : MeasurableSet S) {f : G → ℂ} {w : G} (hwS : ∀ x, w * x ∈ S ↔ x ∈ S) {c : ℂ}
    (hc : c ≠ 1) (hf : ∀ x ∈ S, f (w * x) = c * f x) :
    ∫ x in S, f x ∂μ = 0 := by
  set I := ∫ x in S, f x ∂μ with hI
  have key : I = c * I := by
    have h1 := integral_mul_left_eq_self (μ := μ) (S.indicator f) w
    rw [hI, ← integral_indicator hS]
    conv_lhs => rw [← h1]
    rw [← integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem ((hwS x).mpr hx), Set.indicator_of_mem hx, hf x hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((hwS x).mp h)), Set.indicator_of_notMem hx,
        mul_zero]
  have h0 : (1 - c) * I = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

/-- The additive analogue of `setIntegral_eq_zero_of_mul_left`. -/
theorem setIntegral_eq_zero_of_add_right {A : Type*} [AddGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (μ : Measure A) [μ.IsAddRightInvariant] {S : Set A}
    (hS : MeasurableSet S) {f : A → ℂ} {t : A} (htS : ∀ x, x + t ∈ S ↔ x ∈ S) {c : ℂ}
    (hc : c ≠ 1) (hf : ∀ x ∈ S, f (x + t) = c * f x) :
    ∫ x in S, f x ∂μ = 0 := by
  set I := ∫ x in S, f x ∂μ with hI
  have key : I = c * I := by
    have h1 := integral_add_right_eq_self (μ := μ) (S.indicator f) t
    rw [hI, ← integral_indicator hS]
    conv_lhs => rw [← h1]
    rw [← integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem ((htS x).mpr hx), Set.indicator_of_mem hx, hf x hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((htS x).mp h)), Set.indicator_of_notMem hx,
        mul_zero]
  have h0 : (1 - c) * I = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

end Invariance

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] (N : Normalization F)

/-- Integral units are exactly the units of valuation one. -/
theorem mem_integralUnits_iff {u : Fˣ} :
    u ∈ integralUnits (valuation F).integer ↔ valuation F (u : F) = 1 := by
  rw [mem_integralUnits, Valuation.mem_integer_iff, Valuation.mem_integer_iff,
    Units.val_inv_eq_inv_val, map_inv₀]
  have h0 : 0 < valuation F (u : F) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr u.ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ h0).mp h2)
  · intro h
    simp [h]

/-- The principal unit level `1 + ϖ ^ m O`, with `m = 0` giving the integral units. -/
def unitLevel (m : ℕ) : Subgroup Fˣ where
  carrier := {u | valuation F (u : F) = 1 ∧ (u : F) - 1 ∈ N.ball m}
  one_mem' := by simp
  mul_mem' {u w} hu hw := by
    refine ⟨by simp [map_mul, hu.1, hw.1], ?_⟩
    have he : ((u * w : Fˣ) : F) - 1 = (u : F) * ((w : F) - 1) + ((u : F) - 1) := by
      push_cast
      ring
    rw [he]
    refine add_mem ?_ hu.2
    have hu0 : (u : F) ∈ N.ball 0 := by
      rw [mem_ball, hu.1, zpow_zero]
    simpa using N.mul_mem_ball hu0 hw.2
  inv_mem' {u} hu := by
    refine ⟨by simp [hu.1], ?_⟩
    have he : ((u⁻¹ : Fˣ) : F) - 1 = -((u⁻¹ : Fˣ) : F) * ((u : F) - 1) := by
      rw [mul_sub, neg_mul, Units.inv_mul]
      ring
    rw [he]
    have hu0 : -((u⁻¹ : Fˣ) : F) ∈ N.ball 0 := by
      rw [mem_ball, Valuation.map_neg, Units.val_inv_eq_inv_val, map_inv₀, hu.1, inv_one,
        zpow_zero]
    simpa using N.mul_mem_ball hu0 hu.2

theorem mem_unitLevel {m : ℕ} {u : Fˣ} :
    u ∈ N.unitLevel m ↔ valuation F (u : F) = 1 ∧ (u : F) - 1 ∈ N.ball m := Iff.rfl

theorem unitLevel_zero : N.unitLevel 0 = integralUnits (valuation F).integer := by
  ext u
  rw [mem_unitLevel, mem_integralUnits_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [mem_ball, Nat.cast_zero, zpow_zero]
  calc valuation F ((u : F) - 1) ≤ max (valuation F (u : F)) (valuation F 1) :=
        Valuation.map_sub _ _ _
    _ = 1 := by simp [h]

theorem unitLevel_antitone {m n : ℕ} (h : m ≤ n) : N.unitLevel n ≤ N.unitLevel m := by
  intro u hu
  exact ⟨hu.1, N.ball_antitone (by exact_mod_cast h) hu.2⟩

theorem unitLevel_le_integralUnits (m : ℕ) :
    N.unitLevel m ≤ integralUnits (valuation F).integer := by
  rw [← N.unitLevel_zero]
  exact N.unitLevel_antitone (Nat.zero_le m)

/-- For positive levels the valuation condition is automatic. -/
theorem mem_unitLevel_iff_of_pos {m : ℕ} (hm : 0 < m) {u : Fˣ} :
    u ∈ N.unitLevel m ↔ (u : F) - 1 ∈ N.ball m := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hlt : valuation F ((u : F) - 1) < 1 := by
    refine (N.mem_ball.mp h).trans_lt ?_
    exact zpow_lt_one₀ N.valuation_ϖ_pos N.hϖ.1 (by exact_mod_cast hm)
  have := Valuation.map_one_add_of_lt (valuation F) hlt
  rwa [add_sub_cancel] at this

section Level

/-- The `m`-th power of the maximal ideal is the lattice `ϖ ^ m O`. -/
theorem mem_maximalIdeal_pow_iff (m : ℕ) (x : (valuation F).integer) :
    x ∈ IsLocalRing.maximalIdeal (valuation F).integer ^ m ↔ (x : F) ∈ N.ball m := by
  rw [Conductor.maximalIdeal_pow_eq_span_jacquetUniformizer _ N.ϖ N.hϖ m,
    Ideal.mem_span_singleton, (Valuation.integer.integers _).dvd_iff_le, mem_ball]
  simp [Conductor.jacquetUniformizerInteger]
  exact Iff.rfl

theorem det_glOne {R : Type*} [CommRing R] (g : Matrix.GeneralLinearGroup (Fin 1) R) :
    ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = (g : Matrix (Fin 1) (Fin 1) R) 0 0 := by
  simp [Matrix.det_unique]

/-- Determinants of the rank-one level subgroup lie in the unit level. -/
theorem determinant_mem_unitLevel {m : ℕ} {g : Matrix.GeneralLinearGroup (Fin (0 + 1)) F}
    (hg : g ∈ Conductor.levelSubgroup F 0 m) : GeneralLinear.determinant g ∈ N.unitLevel m := by
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Conductor.mem_integralCongruence_rankOne] at hh
  have hdet : ((GeneralLinear.determinant
      (Matrix.GeneralLinearGroup.map (valuation F).integer.subtype h) : Fˣ) : F) =
      (((h : Matrix (Fin 1) (Fin 1) (valuation F).integer) 0 0 : (valuation F).integer) : F) := by
    rw [det_glOne]
    rfl
  have hunit : IsUnit ((h : Matrix (Fin 1) (Fin 1) (valuation F).integer) 0 0) := by
    have := (Matrix.GeneralLinearGroup.det h).isUnit
    rwa [det_glOne] at this
  refine ⟨?_, ?_⟩
  · rw [hdet]
    exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mp hunit
  · rw [hdet]
    simpa using (N.mem_maximalIdeal_pow_iff m _).mp hh

/-- Every element of the unit level is the determinant of a level element. -/
theorem exists_determinant_eq {m : ℕ} {u : Fˣ} (hu : u ∈ N.unitLevel m) :
    ∃ g ∈ Conductor.levelSubgroup F 0 m, GeneralLinear.determinant g = u := by
  have h1 : (u : F) ∈ (valuation F).integer := by
    rw [Valuation.mem_integer_iff, hu.1]
  have h2 : ((u⁻¹ : Fˣ) : F) ∈ (valuation F).integer := by
    rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, hu.1, inv_one]
  let w : (valuation F).integerˣ :=
    ⟨⟨u, h1⟩, ⟨_, h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  refine ⟨Matrix.GeneralLinearGroup.map (valuation F).integer.subtype
    (Matrix.GeneralLinearGroup.scalar (Fin 1) w), Subgroup.mem_map_of_mem _ ?_, ?_⟩
  · rw [Conductor.mem_integralCongruence_rankOne, N.mem_maximalIdeal_pow_iff]
    simpa [w] using hu.2
  · ext
    rw [det_glOne]
    simp [w]

/-- Triviality on a rank-one level subgroup is triviality on the unit level. -/
theorem level_trivial_iff (χ : Fˣ →* ℂˣ) (m : ℕ) :
    (∀ g ∈ Conductor.levelSubgroup F 0 m, χ (GeneralLinear.determinant g) = 1) ↔
      ∀ u ∈ N.unitLevel m, χ u = 1 := by
  constructor
  · intro h u hu
    obtain ⟨g, hg, rfl⟩ := N.exists_determinant_eq hu
    exact h g hg
  · intro h g hg
    exact h _ (N.determinant_mem_unitLevel hg)

/-- `a` is the exact conductor of `η` on the unit levels. -/
def IsUnitConductor (η : Fˣ →* ℂˣ) (a : ℕ) : Prop :=
  (∀ u ∈ N.unitLevel a, η u = 1) ∧ ∀ b < a, ∃ u ∈ N.unitLevel b, η u ≠ 1

theorem isUnitConductor_iff (η : Fˣ →* ℂˣ) (a : ℕ) :
    N.IsUnitConductor η a ↔
      (∀ g ∈ Conductor.levelSubgroup F 0 a, η (GeneralLinear.determinant g) = 1) ∧
        ∀ b < a, ∃ g ∈ Conductor.levelSubgroup F 0 b, η (GeneralLinear.determinant g) ≠ 1 := by
  rw [IsUnitConductor, N.level_trivial_iff]
  refine and_congr Iff.rfl (forall₂_congr fun b _ => ?_)
  have := (N.level_trivial_iff η b).not
  push Not at this
  exact this.symm

theorem IsUnitConductor.inv {η : Fˣ →* ℂˣ} {a : ℕ} (h : N.IsUnitConductor η a) :
    N.IsUnitConductor η⁻¹ a := by
  refine ⟨fun u hu => by simp [h.1 u hu], fun b hb => ?_⟩
  obtain ⟨u, hu, hne⟩ := h.2 b hb
  exact ⟨u, hu, by simpa using hne⟩

end Level

end Normalization

end Langlands.GodementJacquet.LocalTate
