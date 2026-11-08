import Langlands.Representation.RankinSelberg.HighlyRamified.DualValue
import Langlands.Representation.RankinSelberg.TwistInvariance

/-!
# The dual integrand on the lower-block chart

On a lower-block representative `h = [[A,0],[x,c]]` the dual corank-one integrand of the
candidate test function separates into a factor depending only on `c` and a factor
depending on `(A, x)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear Langlands.Whittaker HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] {m : ℕ}

omit [Field F] in
theorem determinant_inverseTranspose {R : Type*} [CommRing R] {n : ℕ}
    (g : GeneralLinearGroup (Fin n) R) :
    determinant (inverseTranspose n R g) = (determinant g)⁻¹ := by
  apply Units.ext
  simp only [determinant, Matrix.GeneralLinearGroup.val_det_apply, inverseTranspose_coe,
    Matrix.det_transpose]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem determinant_lowerBlockPair (A : GeneralLinearGroup (Fin (m + 1)) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) (c : lowerTriangularSubgroup 1 F) :
    determinant (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) =
      determinant A * determinant c.val := by
  apply Units.ext
  simp only [determinant, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
  have h := det_lowerBlockLocalization (c := 0) A x c
  rw [lowerBlockLocalization, det_rankInclusion] at h
  exact h

theorem lowerBlockPair_eq_mul_diag (A : GeneralLinearGroup (Fin (m + 1)) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) (c : lowerTriangularSubgroup 1 F) :
    (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) =
      lowerBlockPair A x 1 * lowerBlockPair 1 0 c := by
  rw [lowerBlockPair_mul_lowerBlockPair]
  simp

section Pointwise

variable [TopologicalSpace F] [ValuativeRel F]

omit [TopologicalSpace F] [ValuativeRel F] in
theorem det_gl_one_val (c : GeneralLinearGroup (Fin 1) F) :
    ((determinant c : Fˣ) : F) = c 0 0 := by
  simp [determinant, Matrix.det_unique]

/-- If the reversed last row of `h` is not integral, a Whittaker function right invariant
under the level subgroup vanishes at `M(h)`: integral first-row translations act through the
nontrivial phase `ψ(z ξ_k)`. -/
theorem whittaker_dualConj_eq_zero_of_not_integral {f : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ (m + 2))
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F (m + 2) f → W.val (g * k) = W.val g)
    (hψ : ∀ t : F, t ∉ (ValuativeRel.valuation F).integer →
      ∃ z ∈ (ValuativeRel.valuation F).integer, ψ.complex (z * t) ≠ 1)
    (h : GeneralLinearGroup (Fin (m + 2)) F) (k : Fin (m + 2))
    (hk : reversedLastRow h k ∉ (ValuativeRel.valuation F).integer) :
    W.val (dualConj h) = 0 := by
  obtain ⟨z₀, hz₀, hψz⟩ := hψ _ hk
  set z : Fin (m + 2) → F := Pi.single k z₀ with hz
  have hzint : ∀ j, z j ∈ (ValuativeRel.valuation F).integer := by
    intro j
    by_cases hj : j = k
    · subst hj; simp [hz, hz₀]
    · simp [hz, hj]
  have h1 := hK (dualConj h) (firstRowUnipotent z) (firstRowUnipotent_mem_levelSubgroup z hzint)
  rw [whittaker_mul_firstRowUnipotent ψ W (dualConj h) (dualConj_col_zero h) z] at h1
  have hsum : (∑ j, z j * (dualConj h)⁻¹ j.succ 1) = z₀ * reversedLastRow h k := by
    rw [Finset.sum_eq_single k]
    · simp [hz, dualConj_inv_succ_one, reversedLastRow]
    · intro j _ hj
      simp [hz, hj]
    · simp
  rw [hsum] at h1
  have h2 : (ψ.complex (z₀ * reversedLastRow h k) - 1) * W.val (dualConj h) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hψz)

/-- The dual candidate integrand on `[[A,0],[x,c]]` separates into a `c`-factor and an
`(A, x)`-factor. -/
theorem candidateTest_dual_lowerBlockPair {f : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (χ : Fˣ →* ℂˣ) (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F))
    (Φ : (Fin (m + 2) → F) → ℂ) (S1 : F → ℂ) (S2 : (Fin (m + 1) → F) → ℂ) (η : F → ℂ)
    (fdual : GeneralLinearGroup (Fin (m + 2)) F → ℂ) (abv : AbsoluteValue F ℝ)
    (hψ : ∀ t : F, t ∉ (ValuativeRel.valuation F).integer →
      ∃ z ∈ (ValuativeRel.valuation F).integer, ψ.complex (z * t) ≠ 1)
    (hfac : ∀ ξ : Fin (m + 2) → F, (∀ k, ξ k ∈ (ValuativeRel.valuation F).integer) →
      finiteFourier ψ T Φ ξ = S1 (ξ 0) * S2 (fun k => ξ k.succ))
    (hS1 : ∀ c, S1 c ≠ 0 → c ∈ (ValuativeRel.valuation F).integer ∧ c ≠ 0 ∧
      c⁻¹ ∈ (ValuativeRel.valuation F).integer)
    (hS2 : ∀ v, S2 v ≠ 0 → ∀ k, ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (y : F) = v k)
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F (m + 2) f → W.val (g * k) = W.val g)
    (hη : ∀ (y : GeneralLinearGroup (Fin (m + 2)) F) (c : lowerTriangularSubgroup 1 F),
      c.val 0 0 ∈ (ValuativeRel.valuation F).integer →
      (c.val 0 0)⁻¹ ∈ (ValuativeRel.valuation F).integer →
        fdual (y * (lowerBlockPair 1 0 c : GeneralLinear (m + 1 + 1) F)) =
          η (c.val 0 0) * fdual y)
    (habv : ∀ c : F, c ∈ (ValuativeRel.valuation F).integer → c ≠ 0 →
      c⁻¹ ∈ (ValuativeRel.valuation F).integer → abv c = 1)
    (A : GeneralLinearGroup (Fin (m + 1)) F) (x : Matrix (Fin 1) (Fin (m + 1)) F)
    (c : lowerTriangularSubgroup 1 F) (s : ℂ) :
    candidateTest ψ χ W T Φ (weylLong (m + 3) F * inverseTranspose (m + 3) F
        (rankInclusion 1 (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F))) *
      fdual (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) *
      RankinSelberg.determinantWeight abv (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F)
        (s - 1 / 2) =
    (χ (determinant (weylLong (m + 3) F)) : ℂ) *
      (S1 (c.val 0 0) * ((χ (determinant c.val) : ℂ))⁻¹ * η (c.val 0 0)) *
      (S2 (fun k => x 0 k.rev) * ((χ (determinant A) : ℂ))⁻¹ *
        fdual (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F) *
        RankinSelberg.determinantWeight abv A (s - 1 / 2) *
        W.val (dualConj (rankInclusion 1 A))) := by
  rw [candidateTest_dual]
  have hξ0 := reversedLastRow_lowerBlockPair_zero A x c
  have hξs := reversedLastRow_lowerBlockPair_succ A x c
  by_cases hintg : ∀ k, reversedLastRow (m := m)
      (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) k ∈ (ValuativeRel.valuation F).integer
  swap
  · push Not at hintg
    obtain ⟨k, hk⟩ := hintg
    rw [whittaker_dualConj_eq_zero_of_not_integral ψ W hK hψ _ k hk]
    have hzero : S1 (c.val 0 0) * S2 (fun k => x 0 k.rev) = 0 := by
      refine Fin.cases ?_ (fun j hj => ?_) k hk
      · intro h0
        rw [hξ0] at h0
        by_contra hne
        exact h0 (hS1 _ (left_ne_zero_of_mul hne)).1
      · rw [hξs] at hj
        by_contra hne
        obtain ⟨y, -, hye⟩ := hS2 _ (right_ne_zero_of_mul hne) j
        exact hj (hye ▸ y.property)
    linear_combination (-((χ (determinant (weylLong (m + 3) F)) : ℂ) *
      ((χ (determinant c.val) : ℂ))⁻¹ * η (c.val 0 0) * ((χ (determinant A) : ℂ))⁻¹ *
      fdual (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F) *
      RankinSelberg.determinantWeight abv A (s - 1 / 2) *
      W.val (dualConj (rankInclusion 1 A)))) * hzero
  rw [hfac _ hintg, hξ0]
  simp_rw [hξs]
  by_cases hz : S1 (c.val 0 0) * S2 (fun k => x 0 k.rev) = 0
  · rcases mul_eq_zero.mp hz with h | h <;> simp [h]
  · have h1 : S1 (c.val 0 0) ≠ 0 := left_ne_zero_of_mul hz
    have h2 : S2 (fun k => x 0 k.rev) ≠ 0 := right_ne_zero_of_mul hz
    obtain ⟨hc0, hcne, hcinv⟩ := hS1 _ h1
    have hsupp : IsDualSupport (m := m) f
        (reversedLastRow (m := m) (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hξ0]; exact hc0
      · rw [hξ0]; exact hcne
      · rw [hξ0]; exact hcinv
      · intro k
        obtain ⟨y, hy, hye⟩ := hS2 _ h2 k
        exact ⟨y, hy, by rw [hξs, hye]⟩
    rw [whittaker_dualConj_lowerBlockPair W.val hK A x c hsupp]
    rw [lowerBlockPair_eq_mul_diag A x c, hη _ c hc0 hcinv, ← lowerBlockPair_eq_mul_diag A x c]
    -- determinants
    have hdet : determinant (weylLong (m + 3) F * inverseTranspose (m + 3) F
        (rankInclusion 1 (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F))) =
        determinant (weylLong (m + 3) F) * (determinant A * determinant c.val)⁻¹ := by
      rw [map_mul, determinant_inverseTranspose, ← determinant_lowerBlockPair]
      congr 2
      apply Units.ext
      simp only [determinant, Matrix.GeneralLinearGroup.val_det_apply]
      exact det_rankInclusion 1 _
    have hweight : RankinSelberg.determinantWeight abv
        (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) (s - 1 / 2) =
        RankinSelberg.determinantWeight abv A (s - 1 / 2) := by
      unfold RankinSelberg.determinantWeight
      have := congrArg (fun u : Fˣ => (u : F)) (determinant_lowerBlockPair A x c)
      simp only [determinant, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul] at this
      rw [this, map_mul]
      have hc1 : abv (Matrix.det c.val.val) = 1 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, ← determinant, det_gl_one_val]
        exact habv _ hc0 hcne hcinv
      rw [hc1, mul_one]
    rw [hdet, hweight]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end Pointwise

end Langlands.RankinSelberg.HighlyRamified
