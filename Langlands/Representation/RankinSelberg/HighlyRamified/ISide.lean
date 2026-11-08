import Langlands.Representation.RankinSelberg.HighlyRamified.TestVector
import Langlands.Representation.RankinSelberg.RecursiveQuotientCoordinates

/-!
# The forward side of Jacquet–Shalika §4.4

Two level-`f` functions with one central character that agree on the mirabolic subgroup
give the same values `Σ_z Φ(z) W_i(diag(g,1) w n(z))` whenever the finite weight `Φ` is
supported on first rows `z` with `z_last⁻¹, z_j / z_last ∈ 𝔭^f`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {n : ℕ}

/-- First rows `z ∈ F^(n+1)` with `z_last ≠ 0`, `z_last⁻¹ ∈ 𝔭^f` and `z_j / z_last ∈ 𝔭^f`. -/
def IsDeepFirstRow (f : ℕ) (z : Fin (n + 1) → F) : Prop :=
  z (Fin.last n) ≠ 0 ∧
    (∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = 1 / z (Fin.last n)) ∧
    ∀ j : Fin n, ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = z j.castSucc / z (Fin.last n)

/-- Pointwise agreement at `diag(g,1) w n(z)` for a deep first row `z`. -/
theorem eq_at_weyl_firstRow {f : ℕ} (ω : Fˣ →* ℂˣ)
    (W₁ W₂ : GeneralLinearGroup (Fin (n + 2)) F → ℂ)
    (hK₁ : ∀ g k, k ∈ Conductor.levelSubgroup F (n + 1) f → W₁ (g * k) = W₁ g)
    (hK₂ : ∀ g k, k ∈ Conductor.levelSubgroup F (n + 1) f → W₂ (g * k) = W₂ g)
    (hZ₁ : ∀ (z : Fˣ) g, W₁ (GeneralLinearGroup.scalar (Fin (n + 2)) z * g) = ω z * W₁ g)
    (hZ₂ : ∀ (z : Fˣ) g, W₂ (GeneralLinearGroup.scalar (Fin (n + 2)) z * g) = ω z * W₂ g)
    (hP : ∀ p : GeneralLinearGroup (Fin (n + 2)) F,
      (∀ j, p (Fin.last (n + 1)) j =
        (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) (Fin.last (n + 1)) j) → W₁ p = W₂ p)
    (g : GeneralLinearGroup (Fin (n + 1)) F) (z : Fin (n + 1) → F) (hz : IsDeepFirstRow f z) :
    W₁ (rankInclusion 1 g * weylLong (n + 2) F * firstRowUnipotent z) =
      W₂ (rankInclusion 1 g * weylLong (n + 2) F * firstRowUnipotent z) := by
  obtain ⟨hzl, hinv, hj⟩ := hz
  set m := rankInclusion 1 g * weylLong (n + 2) F * firstRowUnipotent z with hm
  have hrow : ∀ j, m (Fin.last (n + 1)) j = Fin.cases 1 z j := by
    intro j
    have h := congrFun (lastRow_rankInclusion_one_mul n g
      (weylLong (n + 2) F * firstRowUnipotent z)) j
    rw [hm, mul_assoc]
    change lastRow (rankInclusion 1 g * (weylLong (n + 2) F * firstRowUnipotent z)) j = _
    rw [h]
    exact weylLong_mul_firstRowUnipotent_last z j
  have hlast : m (Fin.last (n + 1)) (Fin.last (n + 1)) = z (Fin.last n) := by
    rw [hrow, ← Fin.succ_last]
    rfl
  apply eq_of_lastRow_congruence ω W₁ W₂ hK₁ hK₂ hZ₁ hZ₂ hP m
  · rw [hlast]; exact hzl
  · intro j hjl
    rw [hlast, hrow]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · obtain ⟨x, hx, hxe⟩ := hinv
      exact ⟨x, hx, by rw [hxe]; rfl⟩
    · have hj' : j' ≠ Fin.last n := by
        intro h
        apply hjl
        rw [h, Fin.succ_last]
      obtain ⟨j'', rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
      obtain ⟨x, hx, hxe⟩ := hj j''
      exact ⟨x, hx, by rw [hxe]; rfl⟩

/-- The forward test values of the two candidates agree. -/
theorem testValue_eq_at_weyl {f : ℕ} (ω : Fˣ →* ℂˣ)
    (W₁ W₂ : GeneralLinearGroup (Fin (n + 2)) F → ℂ)
    (hK₁ : ∀ g k, k ∈ Conductor.levelSubgroup F (n + 1) f → W₁ (g * k) = W₁ g)
    (hK₂ : ∀ g k, k ∈ Conductor.levelSubgroup F (n + 1) f → W₂ (g * k) = W₂ g)
    (hZ₁ : ∀ (z : Fˣ) g, W₁ (GeneralLinearGroup.scalar (Fin (n + 2)) z * g) = ω z * W₁ g)
    (hZ₂ : ∀ (z : Fˣ) g, W₂ (GeneralLinearGroup.scalar (Fin (n + 2)) z * g) = ω z * W₂ g)
    (hP : ∀ p : GeneralLinearGroup (Fin (n + 2)) F,
      (∀ j, p (Fin.last (n + 1)) j =
        (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) (Fin.last (n + 1)) j) → W₁ p = W₂ p)
    (T : Finset (Fin (n + 1) → F)) (Φ : (Fin (n + 1) → F) → ℂ)
    (hT : ∀ z ∈ T, Φ z ≠ 0 → IsDeepFirstRow f z) (g : GeneralLinearGroup (Fin (n + 1)) F) :
    ∑ z ∈ T, Φ z * W₁ (rankInclusion 1 g * weylLong (n + 2) F * firstRowUnipotent z) =
      ∑ z ∈ T, Φ z * W₂ (rankInclusion 1 g * weylLong (n + 2) F * firstRowUnipotent z) := by
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hΦ : Φ z = 0
  · simp [hΦ]
  · rw [eq_at_weyl_firstRow ω W₁ W₂ hK₁ hK₂ hZ₁ hZ₂ hP g z (hT z hz hΦ)]

end Langlands.RankinSelberg.HighlyRamified
