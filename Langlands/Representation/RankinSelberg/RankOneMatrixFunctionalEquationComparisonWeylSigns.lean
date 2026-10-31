import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Representation.RankinSelberg.EqualRankSwapTransport
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockIntegrationProof

/-! Explicit diagonal signs for the rank-one matrix functional equation. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker

universe uK

variable {K : Type uK} [Field K]

/-- The alternating diagonal `diag((-1)^n,...,-1,1)`. -/
def rankOneWeylAlternating (n : ℕ) : Langlands.GeneralLinear (n + 1) K :=
  characterChangeElement (-1 : Kˣ) n

/-- The diagonal that negates the leading coordinate only. -/
def rankOneWeylLeadingSign (n : ℕ) : Langlands.GeneralLinear (n + 1) K :=
  Iwasawa.diagonalUnits fun i => if i = 0 then (-1 : Kˣ) else 1

@[simp] theorem rankOneWeylAlternating_val (n : ℕ) :
    (rankOneWeylAlternating (K := K) n).val =
      Matrix.diagonal (fun i => (-1 : K) ^ (n - i.val)) := by
  simp [rankOneWeylAlternating, characterChangeElement_val]

@[simp] theorem rankOneWeylLeadingSign_val (n : ℕ) :
    (rankOneWeylLeadingSign (K := K) n).val =
      Matrix.diagonal (fun i => if i = 0 then (-1 : K) else 1) := by
  simp only [rankOneWeylLeadingSign, Iwasawa.diagonalUnits_val]
  congr 1
  funext i
  split_ifs <;> simp

@[simp] theorem rankOneWeylAlternating_inv (n : ℕ) :
    (rankOneWeylAlternating (K := K) n)⁻¹ = rankOneWeylAlternating n :=
  characterChangeElement_neg_one_inv (F := K) n

@[simp] theorem rankOneWeylAlternating_mul_self (n : ℕ) :
    rankOneWeylAlternating (K := K) n * rankOneWeylAlternating n = 1 := by
  simpa only [rankOneWeylAlternating_inv] using
    inv_mul_cancel (rankOneWeylAlternating (K := K) n)

@[simp] theorem inverseTranspose_rankOneWeylAlternating (n : ℕ) :
    inverseTranspose (n + 1) K (rankOneWeylAlternating n) =
      rankOneWeylAlternating n :=
  inverseTranspose_characterChangeElement_neg_one (F := K) n

@[simp] theorem rankOneWeylLeadingSign_mul_self (n : ℕ) :
    rankOneWeylLeadingSign (K := K) n * rankOneWeylLeadingSign n = 1 := by
  apply Units.ext
  simp only [Units.val_mul, rankOneWeylLeadingSign_val, Units.val_one,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [hi]
  · simp [hij]

@[simp] theorem rankOneWeylLeadingSign_inv (n : ℕ) :
    (rankOneWeylLeadingSign (K := K) n)⁻¹ = rankOneWeylLeadingSign n :=
  inv_eq_of_mul_eq_one_right (rankOneWeylLeadingSign_mul_self n)

theorem rankOneWeylLeadingSign_commute_blockWeyl (n : ℕ) (hn : 0 < n) :
    Commute (rankOneWeylLeadingSign (K := K) n) (blockWeylAt 0 n hn) := by
  apply Units.ext
  ext i j
  rw [UnequalRankComplementaryConjugationProof.blockWeylAt_eq K 0 n hn]
  change ((rankOneWeylLeadingSign (K := K) n).val *
      (permutation (n + 1) K _).val) i j =
    ((permutation (n + 1) K _).val * (rankOneWeylLeadingSign (K := K) n).val) i j
  simp only [rankOneWeylLeadingSign_val, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [permutation_entry]
  by_cases h : UnequalRankComplementaryConjugationProof.tailRevPerm 0 n j = i
  · rw [ite_eq_left h]
    have hz : i = 0 ↔ j = 0 := by
      have h0 : UnequalRankComplementaryConjugationProof.tailRevPerm 0 n 0 = 0 := by
        change UnequalRankComplementaryConjugationProof.tailRev 0 n (0 : Fin (n + 1)) = 0
        exact UnequalRankComplementaryConjugationProof.tailRev_of_lt 0 n (i := 0) (by simp)
      constructor
      · intro hi
        have he : UnequalRankComplementaryConjugationProof.tailRevPerm 0 n j =
            UnequalRankComplementaryConjugationProof.tailRevPerm 0 n 0 := h.trans hi |>.trans h0.symm
        exact (UnequalRankComplementaryConjugationProof.tailRevPerm 0 n).injective he
      · rintro rfl
        exact h.symm.trans h0
    simp only [mul_one, one_mul, hz]
  · rw [ite_eq_right h]
    simp

/-- Signed long representative expressed using the actual unsigned one. -/
def rankOneSignedWeyl (n : ℕ) : Langlands.GeneralLinear (n + 1) K :=
  weylLong (n + 1) K * rankOneWeylAlternating n

/-- Signed complementary representative, with all diagonal signs explicit. -/
def rankOneSignedBlockWeyl (n : ℕ) (hn : 0 < n) :
    Langlands.GeneralLinear (n + 1) K :=
  rankOneWeylAlternating n * rankOneWeylLeadingSign n * blockWeylAt 0 n hn

/-- Right translation by the leading sign converts the signed dual argument
to the actual unsigned dual argument, after alternating conjugation. -/
theorem rankOneSignedWeyl_iota_transport (n : ℕ) (hn : 0 < n)
    (g : Langlands.GeneralLinear (n + 1) K) :
    (rankOneSignedWeyl n * inverseTranspose (n + 1) K g *
      rankOneSignedBlockWeyl n hn) * rankOneWeylLeadingSign n =
    weylLong (n + 1) K *
      inverseTranspose (n + 1) K
        (rankOneWeylAlternating n * g * rankOneWeylAlternating n) *
      blockWeylAt 0 n hn := by
  simp only [rankOneSignedWeyl, rankOneSignedBlockWeyl, map_mul,
    inverseTranspose_rankOneWeylAlternating]
  have hc := rankOneWeylLeadingSign_commute_blockWeyl (K := K) n hn
  simp only [mul_assoc]
  rw [← hc.eq, ← mul_assoc (rankOneWeylLeadingSign n),
    rankOneWeylLeadingSign_mul_self, one_mul]

end Langlands.RankinSelberg
