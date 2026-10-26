import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.UnequalRankSmearingUnipotent
import Langlands.HarmonicAnalysis.RowFourier

/-! The actual upper-column conjugation underlying JPSS Fourier smearing. -/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Whittaker

universe uF

variable {F : Type uF} [Field F]

private theorem sum_initial {d N : ℕ} (hd : d ≤ N) (f : Fin N → F)
    (hf : ∀ i, d ≤ i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin d, f ⟨i.val, lt_of_lt_of_le i.isLt hd⟩ := by
  let e : Fin d ↪ Fin N :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
      fun i j h => Fin.ext (congrArg (fun x : Fin N => x.val) h)⟩
  have hs : ∑ i ∈ Finset.univ.map e, f i = ∑ i : Fin N, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply hf
    by_contra hn
    apply hi
    exact Finset.mem_map.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [← hs, Finset.sum_map]
  rfl

/-- Rows after the rectangular block are the corresponding identity rows. -/
theorem unequalRankMatrix_trailing_row {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin j) (Fin (n + 1)) F)
    (a b : Fin (n + (j + k + 1) + 1)) (ha : n + 1 + j ≤ a.val) :
    unequalRankMatrix j k g X a b = if a = b then 1 else 0 := by
  have ha' : ¬ a.val < n + 1 := by omega
  have ha'' : ¬ (n + 1 ≤ a.val ∧ a.val < n + 1 + j) := by omega
  change (unequalRankMatrix j k g X).val a b = _
  rw [unequalRankMatrix_val]
  simp only [Matrix.add_apply, appendIdentity_entry, dite_eq_right ha',
    rectangularEntries, dite_eq_right ha'', add_zero]

/-- Multiplication by the smearing column is an actual finite row pairing. -/
theorem mul_unequalRankSmearingEntries_apply (n j k : ℕ)
    (A : Matrix (Fin (n + ((j + 1) + k + 1) + 1))
      (Fin (n + ((j + 1) + k + 1) + 1)) F)
    (z : Fin (n + 1) → F)
    (a b : Fin (n + ((j + 1) + k + 1) + 1)) :
    (A * unequalRankSmearingEntries n j k z) a b =
      if b.val = n + j + 2 then
        ∑ i : Fin (n + 1), A a ⟨i.val, by omega⟩ * z i
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hb : b.val = n + j + 2
  · simp only [ite_eq_left hb]
    rw [sum_initial (d := n + 1) (by omega) _ (by
      intro i hi
      simp [unequalRankSmearingEntries, show ¬i.val < n + 1 by omega])]
    apply Finset.sum_congr rfl
    intro i _
    simp [unequalRankSmearingEntries, i.isLt, hb]
  · simp [unequalRankSmearingEntries, hb]

/-- The smearing column is unchanged by right multiplication by the block. -/
theorem unequalRankSmearingEntries_mul_block {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    unequalRankSmearingEntries n j k z * (unequalRankMatrix (j + 1) k g X).val =
      unequalRankSmearingEntries n j k z := by
  let c : Fin (n + ((j + 1) + k + 1) + 1) := ⟨n + j + 2, by omega⟩
  ext a b
  rw [Matrix.mul_apply]
  by_cases ha : a.val < n + 1
  · rw [Fintype.sum_eq_single c]
    · have hrow := unequalRankMatrix_trailing_row (j + 1) k g X c b (by dsimp [c]; omega)
      change _ * unequalRankMatrix (j + 1) k g X c b = _
      rw [hrow]
      have hc : b.val = n + j + 2 ↔ c = b := by
        constructor <;> intro h
        · apply Fin.ext
          exact h.symm
        · exact (congrArg Fin.val h).symm
      simp [unequalRankSmearingEntries, ha, c, hc]
    · intro i hi
      have hi' : i.val ≠ n + j + 2 := by
        intro h
        exact hi (Fin.ext h)
      simp [unequalRankSmearingEntries, ha, hi']
  · simp [unequalRankSmearingEntries, ha]

/-- The actual conjugate in the large general linear group. -/
def unequalRankSmearingConjugate {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F :=
  unequalRankMatrix (j + 1) k g X * unequalRankSmearingUnipotent n j k z *
    (unequalRankMatrix (j + 1) k g X)⁻¹

/-- Its value is the identity plus the block times the supported column. -/
theorem unequalRankSmearingConjugate_val {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    (unequalRankSmearingConjugate g X z).val =
      1 + (unequalRankMatrix (j + 1) k g X).val * unequalRankSmearingEntries n j k z := by
  let B := unequalRankMatrix (j + 1) k g X
  let E := unequalRankSmearingEntries n j k z
  have hEB : E * B.val = E := unequalRankSmearingEntries_mul_block g X z
  have hBi : B.val * (B⁻¹).val = 1 := congrArg Units.val (mul_inv_cancel B)
  have hEi : E * (B⁻¹).val = E := by
    calc
      E * (B⁻¹).val = (E * B.val) * (B⁻¹).val := by rw [hEB]
      _ = E := by rw [mul_assoc, hBi, mul_one]
  change B.val * (1 + E) * (B⁻¹).val = 1 + B.val * E
  rw [mul_add, mul_one, add_mul, hBi, mul_assoc, hEi]

/-- All rows at or after the smearing column vanish in the off-diagonal part. -/
theorem block_mul_unequalRankSmearingEntries_trailing {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F)
    (a b : Fin (n + ((j + 1) + k + 1) + 1)) (ha : n + j + 2 ≤ a.val) :
    ((unequalRankMatrix (j + 1) k g X).val * unequalRankSmearingEntries n j k z) a b = 0 := by
  rw [Matrix.mul_apply]
  simp_rw [show ∀ i, (unequalRankMatrix (j + 1) k g X).val a i =
    if a = i then 1 else 0 from fun i =>
      unequalRankMatrix_trailing_row (j + 1) k g X a i (by omega)]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : a = i
  · subst i
    simp only [ite_true, one_mul, unequalRankSmearingEntries,
      dite_eq_right (show ¬a.val < n + 1 by omega)]
  · simp only [ite_eq_right hi, zero_mul]

/-- The computed conjugate belongs to the actual upper-unipotent subgroup. -/
theorem unequalRankSmearingConjugate_mem_upperUnipotent {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    unequalRankSmearingConjugate g X z ∈
      upperUnipotent (n + ((j + 1) + k + 1) + 1) F := by
  have hzero (a b : Fin (n + ((j + 1) + k + 1) + 1)) (hab : b ≤ a) :
      ((unequalRankMatrix (j + 1) k g X).val * unequalRankSmearingEntries n j k z) a b = 0 := by
    by_cases hb : b.val = n + j + 2
    · exact block_mul_unequalRankSmearingEntries_trailing g X z a b (by
        simp only [Fin.le_def] at hab
        omega)
    · simp [mul_unequalRankSmearingEntries_apply, hb]
  constructor
  · intro a b hab
    change b < a at hab
    rw [unequalRankSmearingConjugate_val]
    simp only [Matrix.add_apply, Matrix.one_apply, ite_eq_right (ne_of_gt hab),
      hzero a b (le_of_lt hab), add_zero]
  · intro a
    change (unequalRankSmearingConjugate g X z).val a a = 1
    rw [unequalRankSmearingConjugate_val]
    simp [hzero a a le_rfl]

/-- The middle-leading entries are exactly the supplied rectangular matrix. -/
theorem unequalRankMatrix_middle_leading_entry {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin j) (Fin (n + 1)) F) (a : Fin j) (b : Fin (n + 1)) :
    unequalRankMatrix j k g X ⟨n + 1 + a.val, by omega⟩ ⟨b.val, by omega⟩ = X a b := by
  have ha : ¬ n + 1 + a.val < n + 1 := by omega
  have hr : n + 1 ≤ n + 1 + a.val ∧ n + 1 + a.val < n + 1 + j := by omega
  have hne : (⟨n + 1 + a.val, by omega⟩ : Fin (n + (j + k + 1) + 1)) ≠
      ⟨b.val, by omega⟩ := by
    intro h
    have hval := congrArg Fin.val h
    change n + 1 + a.val = b.val at hval
    omega
  change (unequalRankMatrix j k g X).val _ _ = _
  rw [unequalRankMatrix_val]
  simp only [Matrix.add_apply, appendIdentity_entry, dite_eq_right ha,
    ite_eq_right hne, rectangularEntries, dite_eq_left hr, dite_eq_left b.isLt, zero_add]
  congr 2
  omega

/-- The computed conjugate as an element of the actual subgroup. -/
def unequalRankSmearingUpper {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    upperUnipotent (n + ((j + 1) + k + 1) + 1) F :=
  ⟨unequalRankSmearingConjugate g X z,
    unequalRankSmearingConjugate_mem_upperUnipotent g X z⟩

/-- Only the last rectangular row contributes to the adjacent-entry sum. -/
theorem unequalRankSmearingUpper_superdiagonalSum {n j k : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    (∑ i : Fin (n + ((j + 1) + k + 1)),
      (unequalRankSmearingUpper g X z).val i.castSucc i.succ) =
      ∑ i : Fin (n + 1), X (Fin.last j) i * z i := by
  let i₀ : Fin (n + ((j + 1) + k + 1)) := ⟨n + j + 1, by omega⟩
  rw [Fintype.sum_eq_single i₀]
  · change (unequalRankSmearingConjugate g X z).val i₀.castSucc i₀.succ = _
    rw [unequalRankSmearingConjugate_val]
    simp only [Matrix.add_apply, Matrix.one_apply,
      ite_eq_right (ne_of_lt i₀.castSucc_lt_succ), zero_add,
      mul_unequalRankSmearingEntries_apply,
      ite_eq_left (show i₀.succ.val = n + j + 2 by rfl)]
    apply Finset.sum_congr rfl
    intro i _
    have ha : i₀.castSucc =
        (⟨n + 1 + (Fin.last j).val, by omega⟩ : Fin (n + ((j + 1) + k + 1) + 1)) := by
      apply Fin.ext
      dsimp [i₀]
      omega
    rw [ha, unequalRankMatrix_middle_leading_entry]
  · intro i hi
    have hb : i.succ.val ≠ n + j + 2 := by
      intro h
      apply hi
      apply Fin.ext
      dsimp [i₀]
      simp only [Fin.val_succ] at h
      omega
    change (unequalRankSmearingConjugate g X z).val i.castSucc i.succ = 0
    rw [unequalRankSmearingConjugate_val]
    simp only [Matrix.add_apply, Matrix.one_apply,
      ite_eq_right (ne_of_lt i.castSucc_lt_succ), zero_add,
      mul_unequalRankSmearingEntries_apply, ite_eq_right hb]

variable [TopologicalSpace F]

/-- The standard character of the actual conjugate has the required plus sign. -/
theorem unequalRankSmearingUpper_character (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    {n j k : ℕ} (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    (standardCharacter ψ (n + ((j + 1) + k + 1)) (unequalRankSmearingUpper g X z) : ℂ) =
      ψ.complex (HarmonicAnalysis.rowPairing z (X (Fin.last j))) := by
  rw [standardCharacter_apply, unequalRankSmearingUpper_superdiagonalSum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

universe uV

/-- Covariance converts right smearing at the block to the last-row character. -/
theorem unequalRankMatrix_smearing_coefficient
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F) {n j k : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + ((j + 1) + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F)
    (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F) (z : Fin (n + 1) → F) :
    f.val.val (unequalRankMatrix (j + 1) k g X * unequalRankSmearingUnipotent n j k z) =
      ψ.complex (HarmonicAnalysis.rowPairing z (X (Fin.last j))) *
        f.val.val (unequalRankMatrix (j + 1) k g X) := by
  have he : unequalRankMatrix (j + 1) k g X * unequalRankSmearingUnipotent n j k z =
      (unequalRankSmearingUpper g X z).val * unequalRankMatrix (j + 1) k g X := by
    change _ = (_ * _ * (unequalRankMatrix (j + 1) k g X)⁻¹) * _
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [he, f.val.property, unequalRankSmearingUpper_character]

end Langlands.RankinSelberg
