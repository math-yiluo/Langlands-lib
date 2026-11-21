import Langlands.Global.RankinSelberg.ComplexLocalEqualFiniteSquareNormalized
import Langlands.Global.RankinSelberg.ComplexStandardPairingParameterProof

/-! # The normalized equal-rank chamber factors and central sign -/

noncomputable section

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams_weight)
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ComplexGodement (shiftedCharacter shiftedCharacter_exponent)
open CuspidalPairPartialGammaGlobal

private theorem singletonDenominator_shift (d : ComplexCharacterData) (es : List ComplexCharacterData)
    (z s : ℂ) :
    (complexPairLFactor [shiftedCharacter d z] es).denominator s =
      (complexPairLFactor [d] es).denominator (s + z) := by
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    denominator_complexLFactor, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [ComplexCharacterData.lFactor, complexTateL, ReciprocalEntire.denominator_shift]
  have hw : ((shiftedCharacter d z).mul e).weight = (d.mul e).weight := rfl
  rw [hw]
  have he : ((shiftedCharacter d z).mul e).exponent = (d.mul e).exponent + z := by
    change d.exponent + z + e.exponent = d.exponent + e.exponent + z
    ring
  rw [he]
  exact congrArg gammaComplex.denominator (by ring)

private theorem pairFactor_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es =
      (complexPairLFactor [d] es).mul (complexPairLFactor ds es) := by
  simpa only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using complexLFactor_append (es.map d.mul) (complexPairBlocks ds es)

/-- The two normalized denominator blocks are the full shifted equal-rank denominator. -/
theorem equalDoubleDenominator_eq_pair (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (z s : ℂ) :
    equalDoubleDenominator d ds es z s = (complexPairLFactor (shiftedCharacter d z :: ds) es).denominator s := by
  rw [equalDoubleDenominator, pairFactor_cons (shiftedCharacter d z) ds es,
    ReciprocalEntire.denominator_mul, singletonDenominator_shift,
    complexPairLFactor_denominator_comm es ds, mul_comm]

theorem shiftedCharacter_inv_eq (d : ComplexCharacterData) (z : ℂ) :
    (shiftedCharacter d z).inv = shiftedCharacter d.inv (-z) := by
  have hw : (shiftedCharacter d z).inv.weight = (shiftedCharacter d.inv (-z)).weight := rfl
  have he : (shiftedCharacter d z).inv.exponent = (shiftedCharacter d.inv (-z)).exponent := by
    change -(d.exponent + z) = -d.exponent + -z
    ring
  refine ComplexStandardPairing.complexCharacterData_ext ?_ hw he
  ext w
  rw [(shiftedCharacter d z).inv.character_eq, (shiftedCharacter d.inv (-z)).character_eq, hw, he]

/-- The dual normalized denominator is the full pair factor of the inverse character lists. -/
theorem equalDoubleDualDenominator_eq_pair (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (z s : ℂ) :
    equalDoubleDualDenominator d ds es z s =
      (complexPairLFactor ((shiftedCharacter d z :: ds).map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator s := by
  rw [equalDoubleDualDenominator, equalDoubleDenominator_eq_pair,
    List.map_cons, shiftedCharacter_inv_eq]

private theorem standardEpsilon_cons_shift (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (z : ℂ) :
    (complexPairStandardEpsilon (shiftedCharacter d z :: ds) es : ℂ) =
      (complexPairStandardEpsilon [d] es : ℂ) * (complexPairStandardEpsilon ds es : ℂ) := by
  simp only [complexPairStandardEpsilon, coe_complexStandardEpsilon, complexPairBlocks,
    List.flatMap_cons, List.map_append, List.prod_append, List.flatMap_nil, List.append_nil,
    List.map_map, Function.comp_def]
  rfl

private theorem standardEpsilon_comm (ds es : List ComplexCharacterData) :
    complexPairStandardEpsilon ds es = complexPairStandardEpsilon es ds := by
  rw [← complexPairEpsilon_one ds es 0, ← complexPairEpsilon_one es ds 0, complexPairEpsilon_comm]

/-- The sign from the dual unfolding turns the double-integral phase into
the local equal-rank epsilon factor with the target central sign. -/
theorem equalDoublePhase_mul_unfolding_sign {r : ℕ} (d : ComplexCharacterData)
    (ds es : List ComplexCharacterData) (hds : ds.length = r + 1) (hes : es.length = r + 2)
    (z s : ℂ) :
    complexCentralSign ds * equalDoublePhase d ds es =
      complexCentralSign es ^ (r + 1) *
        (complexPairEpsilon (shiftedCharacter d z :: ds) es 1 ‖((1 : ℂˣ) : ℂ)‖₊
          (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ) := by
  rw [complexPairEpsilon_one, standardEpsilon_cons_shift, equalDoublePhase,
    standardEpsilon_comm es ds, hds, hes]
  have hs : (complexCentralSign ds ^ (r + 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, complexCentralSign_sq, one_pow]
  calc
    _ = (complexCentralSign ds ^ (r + 2)) ^ 2 *
      (complexCentralSign es ^ (r + 1) *
        ((complexPairStandardEpsilon [d] es : ℂ) * (complexPairStandardEpsilon ds es : ℂ))) := by
      rw [show r + 2 = (r + 1) + 1 from rfl, pow_succ (complexCentralSign ds) (r + 1)]
      ring
    _ = _ := by rw [hs, one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
