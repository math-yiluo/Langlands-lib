import Langlands.Representation.RankinSelberg.TwoBlockDominantDiagonalBlocks

/-! # Actual rectangle support at two-block Levi elements -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockLowerUnipotentQuotient

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- Unsigned permutation matrices belong to the actual integral subgroup. -/
theorem permutation_mem_integralOpen (n : ℕ) (s : Equiv.Perm (Fin (n + 1))) :
    permutation (n + 1) F.Carrier s ∈ integralOpen F n := by
  rw [mem_integralOpen]
  constructor <;> intro i l
  · rw [permutation_entry]
    split <;> simp
  · rw [permutation_inv, permutation_entry]
    split <;> simp

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The right column-alignment permutation is integral. -/
theorem diagonalRightPermutation_mem_integralOpen
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1)) :
    diagonalRightPermutation (K := F.Carrier) h hr ∈ integralOpen F r := by
  apply (integralOpen F r).mul_mem
  · exact permutation_mem_integralOpen F r Fin.revPerm
  · rw [blockWeyl_permutation]
    exact permutation_mem_integralOpen F r _

/-- The actual rank inclusion carries right integral factors to integral factors. -/
theorem append_mem_integralOpen (hr : r = t + (j + k + 1))
    {c : GeneralLinear (t + 1) F.Carrier} (hc : c ∈ integralOpen F t) :
    append hr c ∈ integralOpen F r := by
  have hc' := (mem_integralOpen F c).mp hc
  rw [mem_integralOpen]
  constructor <;> intro i l
  · rw [append_entry]
    split_ifs
    · exact hc'.1 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
  · rw [← map_inv, append_entry]
    split_ifs
    · exact hc'.2 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _

/-- Uniform block support transported only along equality of the actual ranks. -/
theorem exists_reindex_blockSum_rectangular_support
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n j k d r : ℕ)
    (H : n + (j + k + 1) + 1 + (d + 1) = r + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier), IsCompact C ∧
      ∀ (g : GeneralLinear (n + 1) F.Carrier)
        (Y : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
        (D : GeneralLinear (d + 1) F.Carrier)
        (c : GeneralLinear (r + 1) F.Carrier),
        c ∈ integralOpen F r →
        W.val.val (reindex (finCongr H) (blockSum (unequalRankMatrix j k g Y, D)) * c) ≠ 0 →
        Y ∈ C := by
  have hr : r = n + (j + k + 1) + 1 + d := by omega
  subst r
  exact exists_blockSum_rectangular_support F ψ n j k d π hπ ell W

/-- A single compact set bounds the actual reversed second rectangle times
its Levi block, uniformly in the first rectangle and the right integral factor. -/
def IsLeviSecondRectangularSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (C : Set (Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)) : Prop :=
  IsCompact C ∧ ∀ (b : (succBlockShape m h).Levi F.Carrier)
    (c : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F.Carrier b * c) x y) ≠ 0 →
    y.submatrix Fin.rev Fin.rev * (b 1).val ∈ C

/-- Actual compact second-rectangle support for every smooth ambient coefficient. -/
theorem exists_levi_second_rectangular_support
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C, IsLeviSecondRectangularSupport F ψ h hr π ell W C := by
  obtain ⟨C, hC, hsupport⟩ :=
    exists_reindex_blockSum_rectangular_support F ψ (m 1) j 0 (k + m 0) r
      (diagonalBlocksRank h hr) π hπ ell W
  refine ⟨C, hC, fun b c x y hc hW => ?_⟩
  have he : matrix h hr ((succBlockShape m h).leviEmbedding F.Carrier b * c) x y =
      reindex (finCongr (diagonalBlocksRank h hr))
        (blockSum (unequalRankMatrix j 0 (b 1)
          (y.submatrix Fin.rev Fin.rev * (b 1).val),
          trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))) *
        (diagonalRightPermutation h hr * append hr c) := by
    rw [← matrix_levi_diagonalBlocks h hr b x y]
    simp only [matrix, map_mul, mul_assoc, inv_mul_cancel_left]
  apply hsupport (b 1) _ (trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))
    (diagonalRightPermutation h hr * append hr c)
    ((integralOpen F r).mul_mem (diagonalRightPermutation_mem_integralOpen F h hr)
      (append_mem_integralOpen F hr hc))
  simpa only [← he] using hW

end Langlands.RankinSelberg.TwoBlockDominantRectangular
