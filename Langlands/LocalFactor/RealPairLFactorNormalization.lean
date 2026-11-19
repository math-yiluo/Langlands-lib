import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-! # Normalization of the real pair L-factor

Splitting induced blocks of weight zero and replacing negative weights by positive weights
preserve the real pair L-factor in either slot. See the paired Markdown.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.LocalFactor.Archimedean

open Langlands.Archimedean

private theorem gammaReal_duplication (t : ℂ) :
    (gammaReal.shift t).mul (gammaReal.shift (t + 1)) = gammaComplex.shift t := by
  apply ReciprocalEntire.ext
  funext z
  change (Complex.Gammaℝ (z + t))⁻¹ * (Complex.Gammaℝ (z + (t + 1)))⁻¹ =
    (Complex.Gammaℂ (z + t))⁻¹
  rw [← add_assoc, ← mul_inv, Complex.Gammaℝ_mul_Gammaℝ_add_one]

private def pairBlockDenominator (z : ℂ) (x y : RealBlock) : ℂ :=
  (realLFactor (x.tensor y)).denominator z

private theorem pairBlockDenominator_comm (z : ℂ) (x y : RealBlock) :
    pairBlockDenominator z x y = pairBlockDenominator z y x := by
  rcases x with c | d <;> rcases y with e | f
  · simp only [pairBlockDenominator, RealBlock.tensor, realLFactor_singleton,
      RealBlock.lFactor_character, RealCharacterData.mul]
    rw [add_comm c.exponent e.exponent, add_comm c.parity e.parity]
  · rfl
  · rfl
  · have h : Int.natAbs (d.weight + -f.weight) = Int.natAbs (f.weight + -d.weight) := by
      rw [← Int.natAbs_neg (f.weight + -d.weight)]
      congr 1
      omega
    simp only [pairBlockDenominator, RealBlock.tensor, denominator_realLFactor,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      RealBlock.lFactor_induced, ComplexCharacterData.mul, ComplexCharacterData.conj]
    rw [add_comm d.exponent f.exponent, add_comm d.weight f.weight, h]

private theorem pairBlockDenominator_conj (z : ℂ) (d : ComplexCharacterData) (y : RealBlock) :
    pairBlockDenominator z (.induced d.conj) y = pairBlockDenominator z (.induced d) y := by
  rcases y with e | f
  · simp only [pairBlockDenominator, RealBlock.tensor, realLFactor_singleton,
      RealBlock.lFactor_induced, ComplexCharacterData.twistReal, ComplexCharacterData.conj,
      Int.natAbs_neg]
  · have h₁ : Int.natAbs (-d.weight + f.weight) = Int.natAbs (d.weight + -f.weight) := by
      rw [← Int.natAbs_neg (d.weight + -f.weight)]
      congr 1
      omega
    have h₂ : Int.natAbs (-d.weight + -f.weight) = Int.natAbs (d.weight + f.weight) := by
      rw [← Int.natAbs_neg (d.weight + f.weight)]
      congr 1
      omega
    simp only [pairBlockDenominator, RealBlock.tensor, denominator_realLFactor,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      RealBlock.lFactor_induced, ComplexCharacterData.mul, ComplexCharacterData.conj, h₁, h₂]
    exact mul_comm _ _

private theorem gammaReal_parity_pair (z t : ℂ) (e : Fin 2) :
    (gammaReal.shift (t + ((1 + e).val : ℂ))).denominator z *
      (gammaReal.shift (t + ((0 + e).val : ℂ))).denominator z =
    (gammaComplex.shift t).denominator z := by
  have h := congrArg (fun F : ReciprocalEntire => F.denominator z) (gammaReal_duplication t)
  fin_cases e <;> simpa [show (1 + 1 : Fin 2) = 0 by decide, mul_comm] using h

private theorem prod_pairBlockDenominator_expand (z : ℂ) (x y : RealBlock) :
    ((realBlockExpand x).map fun a => pairBlockDenominator z a y).prod =
      pairBlockDenominator z x y := by
  rcases x with c | d
  · simp [realBlockExpand]
  by_cases hw : d.weight = 0
  · rw [realBlockExpand, ite_eq_left hw]
    rcases y with e | f
    · simp only [hw, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, pairBlockDenominator, RealBlock.tensor, realLFactor_singleton,
        RealBlock.lFactor_character, RealBlock.lFactor_induced, RealCharacterData.mul,
        ComplexCharacterData.twistReal, RealJacquetFrobenius.charData, Int.natAbs_zero,
        Nat.cast_zero, zero_div, add_zero]
      exact gammaReal_parity_pair z (d.exponent + e.exponent) e.parity
    · simp only [hw, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, pairBlockDenominator, RealBlock.tensor,
        denominator_realLFactor, RealBlock.lFactor_induced, ComplexCharacterData.twistReal,
        ComplexCharacterData.mul, ComplexCharacterData.conj, RealJacquetFrobenius.charData,
        zero_add, Int.natAbs_neg, add_comm f.exponent d.exponent]
  · simp [realBlockExpand, hw]

/-- Replace a negative induced weight by its positive counterpart. -/
def RealBlock.positiveWeight : RealBlock → RealBlock
  | .character c => .character c
  | .induced d => if d.weight < 0 then .induced d.conj else .induced d

private theorem pairBlockDenominator_positiveWeight (z : ℂ) (x y : RealBlock) :
    pairBlockDenominator z x.positiveWeight y = pairBlockDenominator z x y := by
  cases x with
  | character c => rfl
  | induced d =>
    by_cases h : d.weight < 0
    · simpa only [RealBlock.positiveWeight, ite_eq_left h] using pairBlockDenominator_conj z d y
    · simp only [RealBlock.positiveWeight, ite_eq_right h]

/-- Split weight-zero induced blocks and make the remaining induced weights positive. -/
def realBlockNormalize (x : RealBlock) : List RealBlock :=
  (realBlockExpand x).map RealBlock.positiveWeight

private theorem prod_pairBlockDenominator_normalize (z : ℂ) (x y : RealBlock) :
    ((realBlockNormalize x).map fun a => pairBlockDenominator z a y).prod =
      pairBlockDenominator z x y := by
  simpa only [realBlockNormalize, List.map_map, Function.comp_def,
    pairBlockDenominator_positiveWeight] using prod_pairBlockDenominator_expand z x y

private theorem denominator_flatMap {α : Type*} (xs : List α) (f : α → List RealBlock) (z : ℂ) :
    (realLFactor (xs.flatMap f)).denominator z =
      (xs.map fun x => (realLFactor (f x)).denominator z).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, realLFactor_append, List.map_cons,
      List.prod_cons, ReciprocalEntire.denominator_mul, ih]

private theorem denominator_pair (xs ys : List RealBlock) (z : ℂ) :
    (realPairLFactor xs ys).denominator z =
      (xs.map fun x => (ys.map fun y => pairBlockDenominator z x y).prod).prod := by
  simp only [realPairLFactor, realPairBlocks, denominator_flatMap, pairBlockDenominator]

private theorem prod_prod_comm {α β : Type*} (xs : List α) (ys : List β) (f : α → β → ℂ) :
    (xs.map fun x => (ys.map fun y => f x y).prod).prod =
      (ys.map fun y => (xs.map fun x => f x y).prod).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    rw [List.prod_map_mul]

/-- The real pair L-factor is symmetric in the two presentations. -/
theorem realPairLFactor_comm (xs ys : List RealBlock) :
    realPairLFactor xs ys = realPairLFactor ys xs := by
  apply ReciprocalEntire.ext
  funext z
  rw [denominator_pair, denominator_pair, prod_prod_comm xs ys]
  apply congrArg List.prod
  apply List.map_congr_left
  intro y _
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  exact pairBlockDenominator_comm z x y

/-- Normalizing the first presentation preserves its real pair L-factor. -/
theorem realPairLFactor_normalize_left (xs ys : List RealBlock) :
    realPairLFactor (xs.flatMap realBlockNormalize) ys = realPairLFactor xs ys := by
  apply ReciprocalEntire.ext
  funext z
  simp only [denominator_pair]
  rw [List.map_flatMap, List.flatMap, List.prod_flatten, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  change ((realBlockNormalize x).map
    fun a => (ys.map fun y => pairBlockDenominator z a y).prod).prod =
    (ys.map fun y => pairBlockDenominator z x y).prod
  rw [prod_prod_comm (realBlockNormalize x) ys]
  simp only [prod_pairBlockDenominator_normalize]

/-- Normalizing the second presentation preserves its real pair L-factor. -/
theorem realPairLFactor_normalize_right (xs ys : List RealBlock) :
    realPairLFactor xs (ys.flatMap realBlockNormalize) = realPairLFactor xs ys := by
  rw [realPairLFactor_comm xs, realPairLFactor_normalize_left, realPairLFactor_comm ys]

/-- Permutation of the normalized presentations in both slots preserves the real pair
L-factor. -/
theorem realPairLFactor_eq_of_normalize_perm {xs xs' ys ys' : List RealBlock}
    (hx : (xs.flatMap realBlockNormalize).Perm (xs'.flatMap realBlockNormalize))
    (hy : (ys.flatMap realBlockNormalize).Perm (ys'.flatMap realBlockNormalize)) :
    realPairLFactor xs ys = realPairLFactor xs' ys' := by
  simpa only [realPairLFactor_normalize_left, realPairLFactor_normalize_right] using
    realPairLFactor_perm hx hy

end Langlands.LocalFactor.Archimedean
