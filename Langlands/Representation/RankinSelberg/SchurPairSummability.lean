import Langlands.Representation.RankinSelberg.SymmetricGrowthBounds

/-! # Absolute summability of individual Jacobi–Trudi pair terms -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- A geometric product indexed by a finite tuple of natural exponents is summable. -/
theorem summable_pow_sum_fin (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun α : Fin m → ℕ => r ^ (∑ i, α i)) := by
  induction m with
  | zero =>
    let : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun _ => 0)
    exact (hasSum_fintype _).summable
  | succ m ih =>
    have hprod := (summable_geometric_of_lt_one hr0 hr1).mul_of_nonneg ih
      (fun i => pow_nonneg hr0 i) (fun α => pow_nonneg hr0 (∑ i, α i))
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).summable_iff]
    simpa [Function.comp_def, Fin.sum_univ_succ, pow_add, Fin.consEquiv] using hprod

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

/-- A single two-alphabet Jacobi–Trudi term with its total-degree parameter power. -/
def schurPairTerm {m : ℕ} (x : σ → ℂ) (y : τ → ℂ) (t : ℂ) (α : Fin m → ℕ) : ℂ :=
  jacobiTrudiValue x α * jacobiTrudiValue y α * t ^ (∑ i, α i)

/-- Explicit exponential bounds give absolute summability of all natural tuple terms. -/
theorem summable_norm_schurPairTerm_of_bounds {m : ℕ} (x : σ → ℂ) (y : τ → ℂ)
    (Cx Ax Cy Ay : ℝ) (hCx : 0 < Cx) (hAx : 1 ≤ Ax) (_hCy : 0 < Cy) (hAy : 1 ≤ Ay)
    (hX : ∀ α : Fin m → ℕ, ‖jacobiTrudiValue x α‖ ≤ Cx * Ax ^ (∑ i, α i))
    (hY : ∀ α : Fin m → ℕ, ‖jacobiTrudiValue y α‖ ≤ Cy * Ay ^ (∑ i, α i))
    (t : ℂ) (ht : Ax * Ay * ‖t‖ < 1) :
    Summable (fun α : Fin m → ℕ => ‖schurPairTerm x y t α‖) := by
  have hAx0 : 0 ≤ Ax := le_trans zero_le_one hAx
  have hAy0 : 0 ≤ Ay := le_trans zero_le_one hAy
  have hgeo := summable_pow_sum_fin m
    (mul_nonneg (mul_nonneg hAx0 hAy0) (norm_nonneg t)) ht
  apply (hgeo.mul_left (Cx * Cy)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro α
  rw [schurPairTerm, norm_mul, norm_mul, norm_pow]
  have hprod := mul_le_mul (hX α) (hY α) (norm_nonneg _)
    (mul_nonneg hCx.le (pow_nonneg hAx0 _))
  calc
    _ ≤ (Cx * Ax ^ (∑ i, α i)) * (Cy * Ay ^ (∑ i, α i)) * ‖t‖ ^ (∑ i, α i) :=
      mul_le_mul_of_nonneg_right hprod (pow_nonneg (norm_nonneg t) _)
    _ = _ := by simp only [mul_pow]; ring

/-- Every fixed pair of alphabets has a positive disk of absolute individual-term convergence. -/
theorem exists_schurPair_radius (m : ℕ) (x : σ → ℂ) (y : τ → ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      Summable (fun α : Fin m → ℕ => ‖schurPairTerm x y t α‖) := by
  obtain ⟨Cx, Ax, hCx, hAx, hX⟩ := exists_jacobiTrudiValue_bound m x
  obtain ⟨Cy, Ay, hCy, hAy, hY⟩ := exists_jacobiTrudiValue_bound m y
  have hAx0 : 0 < Ax := lt_of_lt_of_le zero_lt_one hAx
  have hAy0 : 0 < Ay := lt_of_lt_of_le zero_lt_one hAy
  have hA : 0 < Ax * Ay := mul_pos hAx0 hAy0
  refine ⟨(Ax * Ay)⁻¹, inv_pos.mpr hA, fun t ht => ?_⟩
  apply summable_norm_schurPairTerm_of_bounds x y Cx Ax Cy Ay hCx hAx hCy hAy hX hY t
  calc Ax * Ay * ‖t‖ < Ax * Ay * (Ax * Ay)⁻¹ := mul_lt_mul_of_pos_left ht hA
    _ = 1 := mul_inv_cancel₀ hA.ne'

/-- Restricting to antitone tuples preserves the same absolute convergence. -/
theorem exists_schurPartition_radius (m : ℕ) (x : σ → ℂ) (y : τ → ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      Summable (fun α : {α : Fin m → ℕ // Antitone α} => ‖schurPairTerm x y t α.val‖) := by
  obtain ⟨r, hr, hs⟩ := exists_schurPair_radius m x y
  exact ⟨r, hr, fun t ht => (hs t ht).subtype _⟩

end Langlands.GeneralLinear.Spherical
