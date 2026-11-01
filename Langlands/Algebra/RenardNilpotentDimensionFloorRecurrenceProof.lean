import Langlands.Algebra.RenardNilpotentDimensionFloorRecurrenceStatement
import Langlands.Algebra.RenardNilpotentDimensionBaseCasesProof
import Langlands.Algebra.RenardNilpotentDimensionMonotonicityProof
import Langlands.Algebra.RenardNilpotentMaximizingComplementProof
import Langlands.Algebra.RenardNilpotentHeadTailDimensionProof
import Mathlib.Algebra.Order.Floor.Semiring

namespace Langlands.Renard

private theorem floorArgument_bounds (l k : ℕ) (hk : 1 ≤ k) :
    let q : ℝ := (k : ℝ) - (nilpotentGeneratedPhi l k : ℝ) / (k : ℝ)
    0 ≤ q ∧ ⌊q⌋₊ < k := by
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hupper : nilpotentGeneratedPhi l k ≤ k ^ 2 := by
    simpa only [nilpotentGeneratedPhi, Module.finrank_fin_fun] using
      nilpotentGeneratedMaxDimension_le l (Fin k → ℂ)
  have hupperR : (nilpotentGeneratedPhi l k : ℝ) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast hupper
  have hlower : 1 ≤ nilpotentGeneratedPhi l k := by
    have h := nilpotentDimensionMonotonicity.{0, 0}.2 l hk
    rwa [nilpotentDimensionBaseCases.{0}.2.2.1 l] at h
  have hphipos : (0 : ℝ) < nilpotentGeneratedPhi l k := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hlower)
  have hq : 0 ≤ (k : ℝ) - (nilpotentGeneratedPhi l k : ℝ) / (k : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hkpos).mpr
    simpa only [pow_two] using hupperR
  refine ⟨hq, (Nat.floor_lt hq).mpr ?_⟩
  exact sub_lt_self _ (div_pos hphipos hkpos)

/-- Renard C.I: the actual nilpotent maximum floor recurrence and strict descent. -/
theorem nilpotentDimensionFloorRecurrence :
    NilpotentDimensionFloorRecurrenceStatement := by
  intro l k hl hk
  cases l with
  | zero => omega
  | succ l =>
    let q : ℝ := (k : ℝ) - (nilpotentGeneratedPhi (l + 1) k : ℝ) / (k : ℝ)
    have hq := floorArgument_bounds (l + 1) k hk
    change 0 ≤ q ∧ ⌊q⌋₊ < k at hq
    change 0 ≤ q ∧ ⌊q⌋₊ < k ∧
      nilpotentGeneratedPhi (l + 1) k ≤
        nilpotentGeneratedPhi (l + 1) ⌊q⌋₊ + nilpotentGeneratedPhi l k
    refine ⟨hq.1, hq.2, ?_⟩
    obtain ⟨a, hcomm, hnil, hatt, ⟨W, hW⟩, hmaxdim⟩ :=
      nilpotentMaximizingComplement.{0} (Fin k → ℂ) (l + 1)
    simp only [Module.finrank_fin_fun] at hatt
    let s := Module.finrank ℂ W
    have hs : s ≤ k := by
      simpa only [Module.finrank_fin_fun] using W.finrank_le
    have hdim : nilpotentGeneratedPhi (l + 1) k ≤ s * k := by
      simpa only [Module.finrank_fin_fun] using hmaxdim W hW
    have hsplit : nilpotentGeneratedPhi (l + 1) k ≤
        nilpotentGeneratedPhi l k + nilpotentGeneratedPhi (l + 1) (k - s) := by
      simpa only [Module.finrank_fin_fun, hatt] using
        (nilpotentHeadTailDimension.{0} (Fin k → ℂ) l a hcomm hnil).2.2.2.2 W hW
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    have hdimR : (nilpotentGeneratedPhi (l + 1) k : ℝ) ≤ (s : ℝ) * (k : ℝ) := by
      exact_mod_cast hdim
    have hquot : (nilpotentGeneratedPhi (l + 1) k : ℝ) / (k : ℝ) ≤ (s : ℝ) :=
      (div_le_iff₀ hkpos).mpr hdimR
    have hsub : ((k - s : ℕ) : ℝ) ≤ q := by
      rw [Nat.cast_sub hs]
      dsimp [q]
      linarith
    have hindex : k - s ≤ ⌊q⌋₊ := (Nat.le_floor_iff hq.1).mpr hsub
    have hmono := nilpotentDimensionMonotonicity.{0, 0}.2 (l + 1) hindex
    omega

end Langlands.Renard
