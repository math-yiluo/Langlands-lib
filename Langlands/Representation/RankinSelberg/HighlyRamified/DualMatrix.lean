import Langlands.Representation.RankinSelberg.HighlyRamified.TestVector
import Langlands.Representation.Whittaker.Iwasawa

/-!
# The dual matrices of the corank-one dual integral

For `h ∈ GL_(n+1)(F)` the dual corank-one integral evaluates the candidate at
`w ᵗdiag(h,1)⁻¹`. The matrix `M(h) = w ᵗdiag(h,1)⁻¹ w` is `diag(1, w ᵗh⁻¹ w)`; it is a
group homomorphism in `h`, has first column `e_0`, and the entry `(M(h)⁻¹)_(k+1,1)` is the
entry `h_(last, rev k)` of the last row of `h`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F] {n : ℕ}

/-- `M(h) = w · ᵗdiag(h,1)⁻¹ · w` in `GL_(n+2)`. -/
def dualConj : GeneralLinearGroup (Fin (n + 1)) F →* GeneralLinearGroup (Fin (n + 2)) F where
  toFun h := weylLong (n + 2) F * inverseTranspose (n + 2) F (rankInclusion 1 h) *
    weylLong (n + 2) F
  map_one' := by simp
  map_mul' h₁ h₂ := by
    simp only [map_mul]
    rw [show weylLong (n + 2) F * (inverseTranspose (n + 2) F (rankInclusion 1 h₁) *
        inverseTranspose (n + 2) F (rankInclusion 1 h₂)) * weylLong (n + 2) F =
      weylLong (n + 2) F * inverseTranspose (n + 2) F (rankInclusion 1 h₁) *
        (weylLong (n + 2) F * weylLong (n + 2) F) *
        inverseTranspose (n + 2) F (rankInclusion 1 h₂) * weylLong (n + 2) F by
      rw [weylLong_mul_self]; group]
    group

theorem dualConj_apply (h : GeneralLinearGroup (Fin (n + 1)) F) :
    dualConj h = weylLong (n + 2) F * inverseTranspose (n + 2) F (rankInclusion 1 h) *
      weylLong (n + 2) F := rfl

/-- Entries of `M(h)`: `M(h)_(i,j) = (diag(h,1)⁻¹)_(rev j, rev i)`. -/
theorem dualConj_entry (h : GeneralLinearGroup (Fin (n + 1)) F) (i j : Fin (n + 2)) :
    dualConj h i j = (rankInclusion 1 h)⁻¹ j.rev i.rev := by
  rw [dualConj_apply, weylLong_conjugate_entry, inverseTranspose_entry]

/-- Entries of `M(h)⁻¹ = M(h⁻¹)`: `(M(h)⁻¹)_(i,j) = diag(h,1)_(rev j, rev i)`. -/
theorem dualConj_inv_entry (h : GeneralLinearGroup (Fin (n + 1)) F) (i j : Fin (n + 2)) :
    (dualConj h)⁻¹ i j = rankInclusion 1 h j.rev i.rev := by
  rw [← map_inv, dualConj_entry, ← map_inv, inv_inv]

/-- `M(h)` has first column `e_0`. -/
theorem dualConj_col_zero (h : GeneralLinearGroup (Fin (n + 1)) F) (i : Fin (n + 2)) :
    dualConj h i 0 = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i 0 := by
  rw [dualConj_entry, ← map_inv, Fin.rev_zero]
  rcases Fin.eq_castSucc_or_eq_last i.rev with ⟨i', hi'⟩ | hi'
  · rw [hi', Iwasawa.rankInclusion_last_castSucc]
    have : i ≠ 0 := by
      intro h0
      rw [h0, Fin.rev_zero] at hi'
      exact (Fin.castSucc_lt_last i').ne hi'.symm
    rw [Matrix.one_apply_ne this]
  · rw [hi', Iwasawa.rankInclusion_last_last]
    have : i = 0 := by
      rw [← Fin.rev_rev i, hi', Fin.rev_last]
    rw [this, Matrix.one_apply_eq]

/-- `(M(h)⁻¹)_(k+1, 1) = h_(last, rev k)`. -/
theorem dualConj_inv_succ_one (h : GeneralLinearGroup (Fin (n + 1)) F) (k : Fin (n + 1)) :
    (dualConj h)⁻¹ k.succ 1 = h (Fin.last n) k.rev := by
  rw [dualConj_inv_entry]
  have h1 : (1 : Fin (n + 2)).rev = (Fin.last n).castSucc := by
    ext; simp [Fin.val_rev]
  have h2 : k.succ.rev = k.rev.castSucc := by
    ext; simp [Fin.val_rev]
  rw [h1, h2, Iwasawa.rankInclusion_castSucc_castSucc]

end Langlands.RankinSelberg.HighlyRamified
