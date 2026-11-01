import Langlands.Representation.RankinSelberg.TwoBlockLowerDiagonalFourier
import Langlands.LocalField.Uniformizer

/-! Compact-uniform partial Fourier estimates for the lower integrand. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe u

/-- The Schwartz–Bruhat row translates themselves have finite range on a compact set. -/
theorem finite_rowTranslate_schwartz_range {K : Type u} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} (Φ : SchwartzBruhat (Fin n → K))
    (S : Set (GeneralLinear n K)) (hS : IsCompact S) :
    (Set.range (fun g : S => rowTranslate g.val Φ)).Finite := by
  apply Set.Finite.of_finite_image
    (f := fun Ψ : SchwartzBruhat (Fin n → K) => (Ψ : (Fin n → K) → ℂ))
  · rw [← Set.range_comp]
    exact finite_rowTranslate_range Φ S hS
  · intro Ψ _ Ψ' _ h
    exact Subtype.ext h

end Langlands.HarmonicAnalysis

namespace Langlands.RankinSelberg.TwoBlockLowerUnfolding

open GeneralLinear HarmonicAnalysis TwoBlockLowerUnipotentQuotient

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F.Carrier]
  [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]
variable (ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier)
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

omit [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _] in
/-- Moving the last factor of a group product into the Schwartz function. -/
theorem partialSection_mul (g k : GeneralLinear (t + 1) F.Carrier) :
    partialSection h ψ μ Φ (g * k) =
      partialSection h ψ μ
        (letI := F.canonicalTopologicalData.topology
         letI := isTopologicalRing_carrier F
         rowTranslate k Φ) g := by
  let := F.canonicalTopologicalData.topology
  let := isTopologicalRing_carrier F
  simp only [partialSection, rowTranslate_mul]

/-- One pair of constants works for all compact right translates of the diagonal. -/
theorem exists_partialSection_diagonal_compact_bounds
    (hsd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := F.canonicalTopologicalData.fieldT2
      letI : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F.Carrier))
    (hK : letI := F.canonicalTopologicalData.topology; IsCompact K) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧
      ∀ (d : Fin (t + 1) → F.Carrierˣ) (k : GeneralLinear (t + 1) F.Carrier), k ∈ K →
      ‖partialSection h ψ μ Φ (Iwasawa.diagonalUnits d * k)‖ ≤
        C * (F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (∑ j, (F.canonicalTopologicalData.ord (d j : F.Carrier)).natAbs) ∧
      (partialSection h ψ μ Φ (Iwasawa.diagonalUnits d * k) ≠ 0 →
        F.canonicalTopologicalData.ord (d ((succBlockShape m h).index 0 0) : F.Carrier) ≤ M ∧
        -(M : ℤ) ≤ F.canonicalTopologicalData.ord
          (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F.Carrier)) := by
  classical
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hS := finite_rowTranslate_schwartz_range Φ K hK
  let S := Set.range (fun k : K => rowTranslate k.val Φ)
  let := hS.fintype
  have hb (Ψ : S) := exists_partialSection_diagonal_bounds h ψ μ Ψ.val hsd
  choose Cs Ms hCs hbounds using hb
  obtain ⟨C, hC⟩ := (Set.finite_range Cs).bddAbove
  obtain ⟨M, hM⟩ := (Set.finite_range Ms).bddAbove
  refine ⟨max C 1, M, lt_max_of_lt_right one_pos, fun d k hk => ?_⟩
  let Ψ : S := ⟨rowTranslate k Φ, ⟨⟨k, hk⟩, rfl⟩⟩
  have hΨ := hbounds Ψ d
  have hCM : Cs Ψ ≤ max C 1 := (hC (Set.mem_range_self Ψ)).trans (le_max_left _ _)
  have hMM : Ms Ψ ≤ M := hM (Set.mem_range_self Ψ)
  rw [partialSection_mul]
  constructor
  · exact hΨ.1.trans (mul_le_mul_of_nonneg_right hCM (by positivity))
  · intro hne
    obtain ⟨hfirst, hlast⟩ := hΨ.2 hne
    constructor
    · exact hfirst.trans (by exact_mod_cast hMM)
    · have hm : -(M : ℤ) ≤ -(Ms Ψ : ℤ) := neg_le_neg (Int.ofNat_le.mpr hMM)
      exact hm.trans hlast

omit [MeasurableSpace F.Carrier]
  [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _] in
/-- Moving the inverse block rotation through a diagonal permutes its entries. -/
theorem blockRotation_inv_mul_diagonal (d : Fin (t + 1) → F.Carrierˣ) :
    (blockRotation h F.Carrier)⁻¹ * Iwasawa.diagonalUnits d =
      Iwasawa.diagonalUnits
        (fun j => d ((succBlockShape m h).reversePermutation.symm j)) *
      (blockRotation h F.Carrier)⁻¹ := by
  have hc : (blockRotation h F.Carrier)⁻¹ * Iwasawa.diagonalUnits d *
      blockRotation h F.Carrier = Iwasawa.diagonalUnits
        (fun j => d ((succBlockShape m h).reversePermutation.symm j)) := by
    apply Units.ext
    ext i j
    rw [blockRotation_inv_conj_apply]
    change (Matrix.diagonal fun i => (d i : F.Carrier))
        ((succBlockShape m h).reversePermutation.symm i)
        ((succBlockShape m h).reversePermutation.symm j) =
      (Matrix.diagonal fun i => (d ((succBlockShape m h).reversePermutation.symm i) : F.Carrier)) i j
    simp only [Matrix.diagonal_apply,
      (succBlockShape m h).reversePermutation.symm.injective.eq_iff]
  calc
    _ = ((blockRotation h F.Carrier)⁻¹ * Iwasawa.diagonalUnits d *
        blockRotation h F.Carrier) * (blockRotation h F.Carrier)⁻¹ := by group
    _ = _ := by rw [hc]

/-- The compact-uniform row-factor bound in the representatives transported
from the standard quotient. -/
theorem exists_partialSection_rotated_diagonal_compact_bounds
    (hsd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := F.canonicalTopologicalData.fieldT2
      letI : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F.Carrier))
    (hK : letI := F.canonicalTopologicalData.topology; IsCompact K) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧
      ∀ (d : Fin (t + 1) → F.Carrierˣ) (k : GeneralLinear (t + 1) F.Carrier), k ∈ K →
      ‖partialSection h ψ μ Φ
        ((blockRotation h F.Carrier)⁻¹ * Iwasawa.diagonalUnits d * k)‖ ≤
        C * (F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (∑ j, (F.canonicalTopologicalData.ord (d j : F.Carrier)).natAbs) ∧
      (partialSection h ψ μ Φ
        ((blockRotation h F.Carrier)⁻¹ * Iwasawa.diagonalUnits d * k) ≠ 0 →
        F.canonicalTopologicalData.ord
          (d ((succBlockShape m h).reversePermutation.symm
            ((succBlockShape m h).index 0 0)) : F.Carrier) ≤ M ∧
        -(M : ℤ) ≤ F.canonicalTopologicalData.ord
          (d ((succBlockShape m h).reversePermutation.symm
            ((succBlockShape m h).index 1 (Fin.last (m 1)))) : F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let K' := (fun k : GeneralLinear (t + 1) F.Carrier => (blockRotation h F.Carrier)⁻¹ * k) '' K
  have hK' : IsCompact K' := hK.image (continuous_const.mul continuous_id)
  obtain ⟨C, M, hC, hb⟩ := exists_partialSection_diagonal_compact_bounds h ψ μ Φ hsd K' hK'
  refine ⟨C, M, hC, fun d k hk => ?_⟩
  have heq : (blockRotation h F.Carrier)⁻¹ * Iwasawa.diagonalUnits d * k =
      Iwasawa.diagonalUnits (fun j => d ((succBlockShape m h).reversePermutation.symm j)) *
        ((blockRotation h F.Carrier)⁻¹ * k) := by
    rw [blockRotation_inv_mul_diagonal, mul_assoc]
  have hsum := Equiv.sum_comp (succBlockShape m h).reversePermutation.symm
    (fun j => (F.canonicalTopologicalData.ord (d j : F.Carrier)).natAbs)
  rw [heq]
  simpa only [hsum] using hb
    (fun j => d ((succBlockShape m h).reversePermutation.symm j))
    ((blockRotation h F.Carrier)⁻¹ * k) ⟨k, hk, rfl⟩

/-- Specialization to the canonical uniformizer torus, with endpoint cutoffs
at the adjacent standard coordinates on either side of the block cut. -/
theorem exists_partialSection_rotated_torus_compact_bounds
    (hsd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := F.canonicalTopologicalData.fieldT2
      letI : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F.Carrier))
    (hK : letI := F.canonicalTopologicalData.topology; IsCompact K)
    (j : Fin t) (hj : (j : ℕ) = m 1) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧
      ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F.Carrier), k ∈ K →
      ‖partialSection h ψ μ Φ ((blockRotation h F.Carrier)⁻¹ *
        Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
          lam * k)‖ ≤ C * (F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (∑ i, (lam i).natAbs) ∧
      (partialSection h ψ μ Φ ((blockRotation h F.Carrier)⁻¹ *
        Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
          lam * k) ≠ 0 → lam j.succ ≤ M ∧ -(M : ℤ) ≤ lam j.castSucc) := by
  let T := F.canonicalTopologicalData
  have hfirst : (succBlockShape m h).reversePermutation.symm
      ((succBlockShape m h).index 0 0) = j.succ := by
    apply Fin.ext
    rw [val_reversePermutation_symm_index_zero]
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hlast : (succBlockShape m h).reversePermutation.symm
      ((succBlockShape m h).index 1 (Fin.last (m 1))) = j.castSucc := by
    apply Fin.ext
    rw [val_reversePermutation_symm_index_one]
    simp only [Fin.val_last, Fin.val_castSucc]
    exact hj.symm
  obtain ⟨C, M, hC, hb⟩ := exists_partialSection_rotated_diagonal_compact_bounds h ψ μ Φ hsd K hK
  refine ⟨C, M, hC, fun lam k hk => ?_⟩
  have hord (i : Fin (t + 1)) :
      F.canonicalTopologicalData.ord
        ((LocalFactor.PadicAbelian.uniformizerUnit T ^ lam i : F.Carrierˣ) : F.Carrier) =
      lam i := by
    change T.ord _ = _
    simp only [Units.val_zpow_eq_zpow_val,
      LocalFactor.PadicAbelian.uniformizerUnit_coe, T.ord_zpow, T.ord_uniformizer, mul_one]
  simpa only [Iwasawa.torus, hord, hfirst, hlast] using
    hb (fun i => LocalFactor.PadicAbelian.uniformizerUnit T ^ lam i) k hk

/-- Compact-uniform norm and endpoint support bounds in canonical rotated
torus coordinates. -/
structure RotatedTorusBoundData (K : Set (GeneralLinear (t + 1) F.Carrier))
    (j : Fin t) where
  constant : ℝ
  cutoff : ℕ
  constant_pos : 0 < constant
  bounds : ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F.Carrier), k ∈ K →
    ‖partialSection h ψ μ Φ ((blockRotation h F.Carrier)⁻¹ *
      Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        lam * k)‖ ≤ constant * (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (∑ i, (lam i).natAbs) ∧
    (partialSection h ψ μ Φ ((blockRotation h F.Carrier)⁻¹ *
      Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        lam * k) ≠ 0 → lam j.succ ≤ cutoff ∧ -(cutoff : ℤ) ≤ lam j.castSucc)

/-- Chosen compact-uniform bounds at the cut between the rotated blocks. -/
def rotatedTorusBoundData
    (hsd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := F.canonicalTopologicalData.fieldT2
      letI : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F.Carrier))
    (hK : letI := F.canonicalTopologicalData.topology; IsCompact K)
    (j : Fin t) (hj : (j : ℕ) = m 1) :
    RotatedTorusBoundData h ψ μ Φ K j := by
  classical
  let hex := exists_partialSection_rotated_torus_compact_bounds h ψ μ Φ hsd K hK j hj
  exact ⟨hex.choose, hex.choose_spec.choose,
    hex.choose_spec.choose_spec.1, hex.choose_spec.choose_spec.2⟩

end Langlands.RankinSelberg.TwoBlockLowerUnfolding
