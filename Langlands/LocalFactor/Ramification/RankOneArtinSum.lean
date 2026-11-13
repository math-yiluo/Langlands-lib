import Langlands.LocalFactor.Ramification.InertiaConductorProfile
import Langlands.ClassFieldTheory.Local.FiniteConductorStatement

/-!
# The Artin expression of an inertia character through its upper levels

For a character `ρ` of the inertia group of a finite extension, suppose `ρ` is trivial
on the upper ramification group `G^s` exactly when `a ≤ ⌈s⌉` (for every real `s ≥ 0`).
Then the Library's inertia Artin expression of `ρ` is `a`. This is the rank-one case of
Serre, *Local Fields*, VI §2, Proposition 5: the conductor of a character is `0` if it
is unramified and `1 + t` otherwise, `t` its last upper break. The proof uses the
profile formula `inertiaArtinConductor_eq_integral`.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module MeasureTheory Set

universe uK uL

/-- The fixed vectors of a subgroup in a one-dimensional character representation form
the whole line if the character is trivial on the subgroup, and `0` otherwise. -/
theorem finrank_fixedVectors_rankOne {G : Type*} [Group G] (ρ : G →* ℂˣ) (H : Subgroup G)
    [Decidable (∀ h ∈ H, ρ h = 1)] :
    finrank ℂ (fixedVectors (LocalClassField.rankOneCharacterRepresentation ρ) H) =
      if ∀ h ∈ H, ρ h = 1 then 1 else 0 := by
  split_ifs with hH
  · have htop : fixedVectors (LocalClassField.rankOneCharacterRepresentation ρ) H = ⊤ := by
      rw [eq_top_iff]
      intro z _
      change z ∈ Representation.invariants _
      rw [Representation.mem_invariants]
      intro h
      change LocalClassField.rankOneCharacterRepresentation ρ h z = z
      rw [LocalClassField.rankOneCharacterRepresentation_apply, hH h h.2]
      simp
    rw [htop, finrank_top, Module.finrank_self]
  · push Not at hH
    obtain ⟨h, hh, hne⟩ := hH
    have hbot : fixedVectors (LocalClassField.rankOneCharacterRepresentation ρ) H = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      change z ∈ Representation.invariants _ at hz
      rw [Representation.mem_invariants] at hz
      have h1 := hz ⟨h, hh⟩
      change LocalClassField.rankOneCharacterRepresentation ρ h z = z at h1
      rw [LocalClassField.rankOneCharacterRepresentation_apply] at h1
      have hne' : (ρ h : ℂ) ≠ 1 := fun h' => hne (Units.val_eq_one.mp h')
      have h2 : ((ρ h : ℂ) - 1) * z = 0 := by rw [sub_mul, h1, one_mul, sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3) hne'
      · exact (Submodule.mem_bot ℂ).mpr h3
    rw [hbot, finrank_bot]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- **Rank-one Artin expression through upper levels.** If the inertia character `ρ`
is trivial on the upper ramification group `G^s` exactly when `a ≤ ⌈s⌉` (for every
real `s ≥ 0`), then the inertia Artin expression of `ρ` is `a`. -/
theorem inertiaArtinConductor_rankOne_eq_of_upper_levels
    (ρ : inertia T K →* ℂˣ) (a : ℕ)
    (h : ∀ s : ℝ, 0 ≤ s →
      (a ≤ ⌈s⌉₊ ↔ ∀ σ : inertia T K,
        (σ : F.Carrier ≃ₐ[K] F.Carrier) ∈ upperRamificationGroup T K s → ρ σ = 1)) :
    inertiaArtinConductor T K (LocalClassField.rankOneCharacterRepresentation ρ) = a := by
  classical
  set ρ' := LocalClassField.rankOneCharacterRepresentation ρ
  have hprof : ∀ v : ℝ, 0 ≤ v →
      upperCodimensionProfile T K ρ' v = if a ≤ ⌈v⌉₊ then 0 else 1 := by
    intro v hv
    have hiff : (∀ σ ∈ (upperRamificationGroup T K v).subgroupOf (inertia T K), ρ σ = 1) ↔
        a ≤ ⌈v⌉₊ := by
      rw [h v hv]
      exact forall_congr' fun σ => by rw [Subgroup.mem_subgroupOf]
    unfold upperCodimensionProfile inertiaUpperFixedVectors
    rw [finrank_fixedVectors_rankOne, Module.finrank_self]
    by_cases ha : a ≤ ⌈v⌉₊
    · rw [ite_eq_left (hiff.mpr ha), ite_eq_left ha]
      norm_num
    · rw [ite_eq_right (fun h' => ha (hiff.mp h')), ite_eq_right ha]
      norm_num
  set B := max (herbrandPhi T K (ramificationCutoff T K : ℝ)) (a : ℝ)
  have hB0 : (0 : ℝ) ≤ B := le_trans (Nat.cast_nonneg a) (le_max_right _ _)
  have hart := inertiaArtinConductor_eq_integral T K ρ' B (le_max_left _ _)
  rcases Nat.eq_zero_or_eq_succ_pred a with ha0 | ha0
  · have h0 : upperCodimensionProfile T K ρ' 0 = 0 := by
      rw [hprof 0 le_rfl, ite_eq_left (by omega)]
    have hint : ∫ v in (0 : ℝ)..B, upperCodimensionProfile T K ρ' v = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
      intro v hv
      rw [uIcc_of_le hB0] at hv
      rw [hprof v hv.1, ite_eq_left (by omega)]
    rw [h0, hint, add_zero] at hart
    rw [ha0]
    exact_mod_cast hart
  · set n := a.pred
    have hn : (n : ℝ) ≤ B := by
      refine le_trans ?_ (le_max_right _ _)
      exact_mod_cast Nat.pred_le a
    have h0 : upperCodimensionProfile T K ρ' 0 = 1 := by
      rw [hprof 0 le_rfl, ite_eq_right (by simp; omega)]
    have hint1 : ∫ v in (0 : ℝ)..(n : ℝ), upperCodimensionProfile T K ρ' v = n := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)), intervalIntegral.integral_const,
        smul_eq_mul, mul_one, sub_zero]
      intro v hv
      rw [uIcc_of_le (Nat.cast_nonneg n)] at hv
      rw [hprof v hv.1, ite_eq_right]
      intro hle
      have : ⌈v⌉₊ ≤ n := Nat.ceil_le.mpr hv.2
      omega
    have hint2 : ∫ v in (n : ℝ)..B, upperCodimensionProfile T K ρ' v = 0 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le hn (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro v hv
      rw [hprof v (le_trans (Nat.cast_nonneg n) hv.1.le), ite_eq_left]
      have : n < ⌈v⌉₊ := Nat.lt_ceil.mpr hv.1
      omega
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (upperCodimensionProfile_intervalIntegrable T K ρ' 0 n)
      (upperCodimensionProfile_intervalIntegrable T K ρ' n B), hint1, hint2, h0, add_zero] at hart
    have : (a : ℝ) = 1 + n := by
      rw [ha0]
      push_cast
      ring
    rw [← this] at hart
    exact_mod_cast hart

end Langlands.Ramification.Padic
