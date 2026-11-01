import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceDensity
import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData

/-! # Rotated diagonal coordinates and the exact opposing twist -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.RankinSelberg.TwoBlockLowerFixedSlice

open GeneralLinear TwoBlockJacquet TwoBlockDeformation TwoBlockConvergence
  TwoBlockLowerUnipotentQuotient

universe uF

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Exponents in the original block order after moving the inverse rotation
past a standard diagonal. -/
def rotatedExponents (lam : Fin (t + 1) → ℤ) : Fin (t + 1) → ℤ :=
  fun i => lam ((succBlockShape m h).reversePermutation.symm i)

theorem torusSize_rotatedExponents (lam : Fin (t + 1) → ℤ) :
    torusSize (rotatedExponents h lam) = torusSize lam := by
  exact Equiv.sum_comp (succBlockShape m h).reversePermutation.symm
    (fun i => (lam i).natAbs)

set_option maxHeartbeats 1000000 in
/-- The signed exponent sum in standard order is the second original block
sum minus the first original block sum. -/
theorem twistDegree_rotatedExponents (lam : Fin (t + 1) → ℤ)
    (j : Fin t) (hj : j.val = m 1) :
    twistDegree (Finset.Iic j.castSucc) lam =
      (∑ a, rotatedExponents h lam ((succBlockShape m h).index 1 a)) -
        ∑ a, rotatedExponents h lam ((succBlockShape m h).index 0 a) := by
  classical
  have h0 (a : Fin (m 0 + 1)) :
      (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 0 a) ∉
        Finset.Iic j.castSucc := by
    simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, Fin.val_castSucc]
    rw [val_reversePermutation_symm_index_zero h a, hj]
    omega
  have h1 (a : Fin (m 1 + 1)) :
      (succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 1 a) ∈
        Finset.Iic j.castSucc := by
    simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, Fin.val_castSucc]
    rw [val_reversePermutation_symm_index_one h a, hj]
    exact Nat.le_of_lt_succ a.isLt
  let f : Fin (t + 1) → ℤ := fun i =>
    if i ∈ Finset.Iic j.castSucc then lam i else -lam i
  calc
    _ = ∑ x : (succBlockShape m h).Index,
        f ((succBlockShape m h).reversePermutation.symm
          ((succBlockShape m h).indexEquiv x)) :=
      (Equiv.sum_comp ((succBlockShape m h).indexEquiv.trans
        (succBlockShape m h).reversePermutation.symm) f).symm
    _ = (∑ a : Fin (m 0 + 1),
        f ((succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 0 a))) +
      (∑ a : Fin (m 1 + 1),
        f ((succBlockShape m h).reversePermutation.symm ((succBlockShape m h).index 1 a))) := by
      rw [Fintype.sum_sigma, Fin.sum_univ_two]
      rfl
    _ = _ := by
      dsimp only [f]
      simp only [h0, h1, ite_false, ite_true, Finset.sum_neg_distrib, rotatedExponents]
      ring

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

/-- Reassembling the extracted diagonal blocks gives the original torus. -/
theorem torusLevi_embedding (lam : Fin (t + 1) → ℤ) :
    (succBlockShape m h).leviEmbedding F.Carrier (torusLevi F h lam) =
      Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        lam := by
  apply Units.ext
  ext k l
  obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
  obtain ⟨⟨j, b⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective l
  change (succBlockShape m h).leviEmbedding F.Carrier (torusLevi F h lam)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index j b) = _
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same]
    change (Iwasawa.torus _ _) a b = (Iwasawa.torus _ lam)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index i b)
    change (Matrix.diagonal _) a b = (Matrix.diagonal _)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index i b)
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab, ((succBlockShape m h).index i).injective.ne hab]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij]
    change 0 = (Matrix.diagonal _)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index j b)
    have hne : (succBlockShape m h).index i a ≠ (succBlockShape m h).index j b := by
      intro he
      exact hij (congrArg Sigma.fst ((succBlockShape m h).indexEquiv.injective he))
    simp [hne]

/-- The determinant factors of the two opposing twists become precisely
`q` to minus the twist times the signed degree in standard coordinates. -/
theorem torusLevi_rotated_twist (lam : Fin (t + 1) → ℤ)
    (j : Fin t) (hj : j.val = m 1) (u : ℝ) :
    (((F.canonicalTopologicalData.determinantNorm (m 0 + 1)
        (torusLevi F h (rotatedExponents h lam) 0) : ℝ≥0) : ℝ) ^ (-u) *
      ((F.canonicalTopologicalData.determinantNorm (m 1 + 1)
        (torusLevi F h (rotatedExponents h lam) 1) : ℝ≥0) : ℝ) ^ u) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := by
  change (((F.canonicalTopologicalData.determinantNorm (m 0 + 1)
      (Iwasawa.torus _ _) : ℝ≥0) : ℝ) ^ (-u) *
    ((F.canonicalTopologicalData.determinantNorm (m 1 + 1)
      (Iwasawa.torus _ _) : ℝ≥0) : ℝ) ^ u) = _
  rw [determinantNorm_torus F, determinantNorm_torus F,
    ← Real.rpow_intCast, ← Real.rpow_intCast]
  have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one)
  rw [← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq,
    twistDegree_rotatedExponents h lam j hj]
  congr 1
  push_cast
  ring

end Langlands.RankinSelberg.TwoBlockLowerFixedSlice
