import Langlands.Representation.RankinSelberg.HighlyRamified.DualFactor
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Values of the dual test function on lower-block representatives

The candidate test function `F(y) = χ(det y) Σ_z Φ(z) W(y w n(z))` has first dual function
`F̃(g) = F(w ᵗg⁻¹)`. At `diag(h,1)` it equals `χ(det(w ᵗdiag(h,1)⁻¹)) Ŝ(ξ(h)) W(M(h))`, where
`ξ(h)` is the reversed last row of `h` and `Ŝ(ξ) = Σ_z Φ(z) ψ(⟨z, ξ⟩)`. For
`h = [[A,0],[x,c]]` with `Ŝ(ξ(h)) ≠ 0`, the support condition on `Ŝ` gives
`W(M(h)) = W(M(diag(A,1)))`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear Langlands.Whittaker HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] {m : ℕ}

/-- The finite exponential sum `Ŝ(ξ) = Σ_{z ∈ T} Φ(z) ψ(Σ_k z_k ξ_k)`. -/
def finiteFourier (ψ : UnitaryAdditiveCharacter F) {d : ℕ} (T : Finset (Fin d → F))
    (Φ : (Fin d → F) → ℂ) (ξ : Fin d → F) : ℂ :=
  ∑ z ∈ T, Φ z * ψ.complex (∑ k, z k * ξ k)

/-- The candidate test function `y ↦ χ(det y) Σ_z Φ(z) W(y w n(z))`. -/
def candidateTest (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
    (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F))
    (Φ : (Fin (m + 2) → F) → ℂ) (y : GeneralLinearGroup (Fin (m + 3)) F) : ℂ :=
  (χ (determinant y) : ℂ) *
    ∑ z ∈ T, Φ z * W.val (y * weylLong (m + 3) F * firstRowUnipotent z)

/-- The reversed last row `ξ(h)_k = h_(last, rev k)`. -/
def reversedLastRow (h : GeneralLinearGroup (Fin (m + 2)) F) : Fin (m + 2) → F :=
  fun k => h (Fin.last (m + 1)) k.rev

/-- The value of the dual candidate test function at `diag(h, 1)`. -/
theorem candidateTest_dual (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
    (W : WhittakerFunctions ψ (m + 2)) (T : Finset (Fin (m + 2) → F))
    (Φ : (Fin (m + 2) → F) → ℂ) (h : GeneralLinearGroup (Fin (m + 2)) F) :
    candidateTest ψ χ W T Φ (weylLong (m + 3) F * inverseTranspose (m + 3) F (rankInclusion 1 h)) =
      (χ (determinant (weylLong (m + 3) F * inverseTranspose (m + 3) F (rankInclusion 1 h))) : ℂ) *
        (finiteFourier ψ T Φ (reversedLastRow h) * W.val (dualConj h)) := by
  unfold candidateTest
  congr 1
  have hM : weylLong (m + 3) F * inverseTranspose (m + 3) F (rankInclusion 1 h) *
      weylLong (m + 3) F = dualConj h := rfl
  simp_rw [hM]
  rw [finiteFourier, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [whittaker_mul_firstRowUnipotent ψ W (dualConj h) (dualConj_col_zero h) z]
  simp_rw [dualConj_inv_succ_one]
  simp only [reversedLastRow]
  ring

section Support

variable [ValuativeRel F]

/-- Support condition for the dual weights: `ξ_0` is an integral unit and every other
coordinate lies in `𝔭^f`. -/
def IsDualSupport (f : ℕ) (ξ : Fin (m + 2) → F) : Prop :=
  ξ 0 ∈ (ValuativeRel.valuation F).integer ∧ ξ 0 ≠ 0 ∧
    (ξ 0)⁻¹ ∈ (ValuativeRel.valuation F).integer ∧
    ∀ k : Fin (m + 1), ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (y : F) = ξ k.succ

omit [TopologicalSpace F] [ValuativeRel F] in
theorem gl_one_inv_apply (g : GeneralLinearGroup (Fin 1) F) :
    (g⁻¹ : GeneralLinearGroup (Fin 1) F) 0 0 = (g 0 0)⁻¹ := by
  have h := congrFun (congrFun (congrArg (fun u : GeneralLinearGroup (Fin 1) F =>
    (u : Matrix (Fin 1) (Fin 1) F)) (mul_inv_cancel g)) 0) 0
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_one, Matrix.mul_apply,
    Fin.sum_univ_one, Matrix.one_apply_eq] at h
  exact (eq_inv_of_mul_eq_one_right h)

omit [TopologicalSpace F] [ValuativeRel F] in
theorem reversedLastRow_lowerBlockPair_zero (A : GeneralLinearGroup (Fin (m + 1)) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) (c : lowerTriangularSubgroup 1 F) :
    reversedLastRow (m := m) (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) 0 = c.val 0 0 := by
  simp only [reversedLastRow, Fin.rev_zero]
  rw [← natAdd_zero_eq_last, lowerBlockPair_22]

omit [TopologicalSpace F] [ValuativeRel F] in
theorem reversedLastRow_lowerBlockPair_succ (A : GeneralLinearGroup (Fin (m + 1)) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) (c : lowerTriangularSubgroup 1 F) (k : Fin (m + 1)) :
    reversedLastRow (m := m) (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F) k.succ = x 0 k.rev := by
  simp only [reversedLastRow]
  have h2 : k.succ.rev = k.rev.castSucc := by ext; simp [Fin.val_rev]
  rw [h2, ← natAdd_zero_eq_last, show (k.rev.castSucc : Fin (m + 1 + 1)) = k.rev.castAdd 1 from
    rfl, lowerBlockPair_21]

/-- On the dual support, `W(M([[A,0],[x,c]])) = W(M(diag(A,1)))`. -/
theorem whittaker_dualConj_lowerBlockPair {f : ℕ} (W : GeneralLinearGroup (Fin (m + 3)) F → ℂ)
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F (m + 2) f → W (g * k) = W g)
    (A : GeneralLinearGroup (Fin (m + 1)) F) (x : Matrix (Fin 1) (Fin (m + 1)) F)
    (c : lowerTriangularSubgroup 1 F) (hξ : IsDualSupport (m := m) f (reversedLastRow (m := m) (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F))) :
    W (dualConj (lowerBlockPair A x c : GeneralLinear (m + 1 + 1) F)) = W (dualConj (rankInclusion 1 A)) := by
  obtain ⟨h0, hne, hinv, hk⟩ := hξ
  rw [reversedLastRow_lowerBlockPair_zero] at h0 hne hinv
  rw [lowerBlockPair_eq_rankInclusion_mul, map_mul]
  apply hK
  apply dualConj_lowerBlockPair_one_mem
  · intro j
    obtain ⟨y, hy, hye⟩ := hk j.rev
    rw [reversedLastRow_lowerBlockPair_succ, Fin.rev_rev] at hye
    rw [← hye]
    exact y.property
  · obtain ⟨y, hy, hye⟩ := hk (Fin.last m)
    rw [reversedLastRow_lowerBlockPair_succ, Fin.rev_last] at hye
    exact ⟨y, hy, hye⟩
  · exact h0
  · rw [gl_one_inv_apply]
    exact hinv

end Support

end Langlands.RankinSelberg.HighlyRamified
