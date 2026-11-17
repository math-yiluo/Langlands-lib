import Langlands.Representation.Archimedean.RealCharacterPairFiltration
import Langlands.Representation.Archimedean.RealCharacterInducedPushforward
import Langlands.Representation.Archimedean.RealSwapLandingMirror
import Langlands.Representation.Archimedean.RealStandardFiltration

/-!
# Frobenius maps for the induced–character filtration on `GL₃(ℝ)`
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInducedCharacter

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet
open Langlands.LocalFactor.Archimedean

/-! ## Multipliers -/

section Multipliers

/-- The indicator of the modes `|k| ≥ ℓ`. -/
def highIndicator (ℓ : ℕ) (k : ℤ) : ℂ := if (ℓ : ℤ) ≤ |k| then 1 else 0

theorem isSymmetric_highIndicator (ℓ : ℕ) (ε : ℤ) : IsSymmetric ε 1 (highIndicator ℓ) :=
  fun k _ => by simp [highIndicator, abs_neg]

end Multipliers

/-! ## The setup -/

section Setup

variable (d : ComplexCharacterData)

/-- The exponent `a = t + ℓ/2` of the first position of the induction block. -/
def aExp : ℂ := d.exponent + (d.weight.natAbs : ℂ) / 2

/-- The exponent `b = t - ℓ/2` of the second position of the induction block. -/
def bExp : ℂ := d.exponent - (d.weight.natAbs : ℂ) / 2

/-- The character `sgn^{s_a} |·|^a`. -/
def ca (sa : Fin 2) : RealCharacterData := RealJacquetFrobenius.charData sa (aExp d)

/-- The character `sgn^{s_b} |·|^b`. -/
def cb (sb : Fin 2) : RealCharacterData := RealJacquetFrobenius.charData sb (bExp d)

@[simp] theorem ca_exponent (sa : Fin 2) : (ca d sa).exponent = aExp d := rfl
@[simp] theorem cb_exponent (sb : Fin 2) : (cb d sb).exponent = bExp d := rfl
@[simp] theorem ca_parity (sa : Fin 2) : (ca d sa).parity = sa := rfl
@[simp] theorem cb_parity (sb : Fin 2) : (cb d sb).parity = sb := rfl

theorem aExp_sub_bExp : aExp d - bExp d = d.weight.natAbs := by
  simp only [aExp, bExp]
  ring

end Setup

/-! ## The tail maps -/

section Tail

variable {d : ComplexCharacterData} {n : ℕ} {pre post : List RealBlock} {sa sb : Fin 2}

theorem tail_parity (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    Even ((d.weight.natAbs : ℤ) - 1 - pairParity (cb d sb) (ca d sa)) := by
  unfold pairParity
  simp only [cb_parity, ca_parity]
  refine ⟨((d.weight.natAbs : ℤ) - 1 - (((sb.val + sa.val) % 2 : ℕ) : ℤ)) / 2, ?_⟩
  omega

theorem realRank_tail_mid (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n) :
    realRank (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post) =
      n := by
  rw [← hn]
  exact realRank_mid_eq pre post rfl

/-- The Frobenius data of the tail map along the block `[c_b, c_a]` onto the induction block
`d`. -/
theorem data_tail (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    IsBlockFrobData n (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post)
      (pre ++ [RealBlock.induced d] ++ post) (realRank pre) (pairParity (cb d sb) (ca d sa))
      ((-1) ^ sa.val)
      (tailMultiplier d.weight.natAbs (pairParity (cb d sb) (ca d sa)) ((-1) ^ sa.val)) := by
  have hpar := tail_parity hs
  have hε := pairParity_eq (cb d sb) (ca d sa)
  refine IsBlockFrobData.of_mid hn rfl rfl ?_ ?_ ?_
    (isSymmetric_tailMultiplier hl hε hpar (neg_one_pow_sq_fin sa)) ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [realPositionCharacter_neg_one, neg_one_pow_pairParity']
    simp only [realPositionSign]
  · rw [realPositionCharacter_neg_one]
    simp only [realPositionSign]
    rw [neg_one_pow_succ_mod_two hε hpar, neg_one_pow_pairParity']
    rfl
  · rw [realPositionCharacter_neg_one]
    simp only [realPositionSign, Fin.val_zero, pow_zero, ca_parity]
    rw [← sq, neg_one_pow_sq_fin]
  · intro e he j hj hjl
    simp only [realInducedBlockAt, Option.some.injEq] at he
    subst he
    by_contra hne
    have := (tailMultiplier_ne_zero_iff hl hε hpar (neg_one_pow_sq_fin sa) hj).mp hne
    have h1 := Int.abs_eq_natAbs j
    have h2 := Int.abs_eq_natAbs d.weight
    omega

/-- The Frobenius data of the inverse tail map, from the induction block `d` to `[c_b, c_a]`. -/
theorem data_tailInv (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    IsBlockFrobData n (pre ++ [RealBlock.induced d] ++ post)
      (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post)
      (realRank pre) (pairParity (cb d sb) (ca d sa)) ((-1) ^ sa.val)⁻¹
      (fun k => (tailMultiplier d.weight.natAbs (pairParity (cb d sb) (ca d sa))
        ((-1) ^ sa.val) k)⁻¹) := by
  have hpar := tail_parity hs
  have hε := pairParity_eq (cb d sb) (ca d sa)
  have hs' : ((-1 : ℂ) ^ sa.val)⁻¹ = (-1) ^ sa.val :=
    inv_eq_self_of_sq_eq_one (neg_one_pow_sq_fin sa)
  refine IsBlockFrobData.of_mid (realRank_tail_mid hn) rfl rfl ?_ ?_ ?_
    (isSymmetric_tailMultiplier hl hε hpar (neg_one_pow_sq_fin sa)).inv ?_ ?_ ?_
  · rfl
  · rfl
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one]
    simp only [realPositionSign]
    rw [neg_one_pow_succ_mod_two hε hpar]
    simp
  · rw [hs', realPositionCharacter_neg_one]
    simp only [realPositionSign]
    rw [neg_one_pow_succ_mod_two hε hpar, neg_one_pow_pairParity']
    simp only [cb_parity, ca_parity]
    linear_combination -(-1 : ℂ) ^ sb.val * neg_one_pow_sq_fin sa
  · rw [hs', realPositionCharacter_neg_one]
    simp only [realPositionSign, Fin.val_zero, pow_zero, one_mul, ca_parity]
  · intro e he
    simp [realInducedBlockAt] at he

theorem realRank_induced_single : realRank [RealBlock.induced d] = 2 := rfl

theorem realRank_tail_pair :
    realRank [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] = 2 := rfl

/-- `Tail ∘ TailInv = id` on the standard module with the induction block `d`. -/
theorem tail_tailInv (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    (f : RealStandardFiltration.KF n (pre ++ [RealBlock.induced d] ++ post)) :
    blockFrobMap (data_tail hn hl hs) (blockFrobMap (data_tailInv hn hl hs) f) = f := by
  have hpar := tail_parity hs
  have hε := pairParity_eq (cb d sb) (ca d sa)
  refine blockFrobMap_blockFrobMap_eq (data_tailInv hn hl hs) (data_tail hn hl hs) f
    fun j hj hne k hk => ?_
  have hP : tailMultiplier d.weight.natAbs (pairParity (cb d sb) (ca d sa))
      ((-1) ^ sa.val) j = 0 := by
    by_contra hP
    exact hne (mul_inv_cancel₀ hP)
  have hjl : |j| < d.weight.natAbs := by
    refine abs_lt_of_parity hpar hj (not_lt.mp fun hlt => ?_)
    exact (tailMultiplier_ne_zero_iff hl hε hpar (neg_one_pow_sq_fin sa) hj).mpr hlt hP
  have hind : realInducedBlockAt (pre ++ [RealBlock.induced d] ++ post) (realRank pre) =
      some d := by
    have e := realInducedBlockAt_mid pre [RealBlock.induced d] post (j := 0)
      (by rw [realRank_induced_single]; norm_num)
    rwa [add_zero] at e
  refine f.2.1.2 (realRank pre) d hind j ?_ k
  rwa [Int.abs_eq_natAbs d.weight]

/-- The tail map satisfies the recurrence for `δ = b - a + 1 = 1 - ℓ`. -/
theorem isRecurrent_tail (hl : 0 < d.weight.natAbs)
    (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    IsRecurrent (GramFormula.realPositionExponent
        (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post)
        (realRank pre) -
      GramFormula.realPositionExponent
        (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post)
        (realRank pre + 1) + 1)
      (pairParity (cb d sb) (ca d sa))
      (tailMultiplier d.weight.natAbs (pairParity (cb d sb) (ca d sa)) ((-1) ^ sa.val)) := by
  rw [exponent_mid_zero pre post (by rw [realRank_tail_pair]; norm_num),
    exponent_mid_one pre post (by rw [realRank_tail_pair]; norm_num)]
  show IsRecurrent (bExp d - aExp d + 1) _ _
  rw [show bExp d - aExp d + 1 = 1 - (d.weight.natAbs : ℂ) by
    linear_combination -(aExp_sub_bExp d)]
  exact isRecurrent_tailMultiplier hl (pairParity_eq _ _) (tail_parity hs)
    (neg_one_pow_sq_fin sa)

/-- The tail map is an exact intertwiner. -/
theorem modulo_tail (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    IsRealIntertwinerModulo n
      (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post)
      (pre ++ [RealBlock.induced d] ++ post) ⊥ (blockFrobMap (data_tail hn hl hs)) :=
  isRealIntertwinerModulo_blockFrobMap _ (isRecurrent_tail hl hs) ⊥

/-- The tail map is surjective. -/
theorem tail_surjective (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    Function.Surjective (blockFrobMap (data_tail hn hl hs)) :=
  fun f => ⟨_, tail_tailInv hn hl hs f⟩

/-- The block Fourier coefficients of the image of the tail map vanish when those of `g` of
weight `|j| ≥ ℓ` do. -/
theorem tail_eq_zero (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    (g : RealStandardFiltration.KF n
      (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post))
    (hg : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (realRank pre) j g x = 0) :
    blockFrobMap (data_tail hn hl hs) g = 0 := by
  have h := data_tail hn hl hs
  have hpar := tail_parity hs
  have hε := pairParity_eq (cb d sb) (ca d sa)
  refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
  rw [blockFourierCoefficient_blockFrobMap _ _ hk, ZeroMemClass.coe_zero,
    blockFourierCoefficient_zero]
  by_cases hj : Even (j - pairParity (cb d sb) (ca d sa))
  · by_cases hjl : |d.weight| ≤ |j|
    · rw [hg j hjl k hk, mul_zero]
    · have hz : tailMultiplier d.weight.natAbs (pairParity (cb d sb) (ca d sa))
          ((-1) ^ sa.val) j = 0 := by
        by_contra hne
        have := (tailMultiplier_ne_zero_iff hl hε hpar (neg_one_pow_sq_fin sa) hj).mp hne
        rw [Int.abs_eq_natAbs d.weight] at hjl
        omega
      rw [hz, zero_mul]
  · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par g hj k, mul_zero]

/-- The Frobenius data of the projection onto the modes `|k| ≥ ℓ` along `[c_b, c_a]`, with
target `[sgn^{s_b} |·|^a, sgn^{s_a} |·|^b]`. -/
theorem data_high (hn : realRank (pre ++ [RealBlock.character (RealJacquetFrobenius.charData sb
      (aExp d)), RealBlock.character (RealJacquetFrobenius.charData sa (bExp d))] ++ post) = n) :
    IsBlockFrobData n
      (pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post)
      (pre ++ [RealBlock.character (RealJacquetFrobenius.charData sb (aExp d)),
        RealBlock.character (RealJacquetFrobenius.charData sa (bExp d))] ++ post)
      (realRank pre) (pairParity (cb d sb) (ca d sa)) 1 (highIndicator d.weight.natAbs) := by
  refine IsBlockFrobData.of_mid hn rfl rfl rfl rfl ?_ (isSymmetric_highIndicator _ _) ?_ ?_ ?_
  · simp only [realPositionCharacter_neg_one, neg_one_pow_pairParity']
    simp only [realPositionSign]
  · rw [realPositionCharacter_neg_one, mul_one]
    rfl
  · rw [realPositionCharacter_neg_one, mul_one]
    rfl
  · intro e he
    simp [realInducedBlockAt] at he

end Tail

end RealInducedCharacter

end Langlands.Archimedean
