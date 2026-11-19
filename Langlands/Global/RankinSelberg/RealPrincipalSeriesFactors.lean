import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Global.RankinSelberg.RealParameterDeterminant
import Langlands.LocalFactor.Archimedean.RealGammaReflection
import Langlands.Representation.Archimedean.RealBlockPositionData
import Mathlib.Topology.DiscreteSubset

/-! # The pair Gamma multiplier for the real principal-series positions -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open Langlands.Archimedean
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Weil.Archimedean
open RealGammaReflection

private def firstPosition (d : ComplexCharacterData) : RealCharacterData :=
  RealJacquetFrobenius.charData (positionParity d.weight.natAbs)
    (d.exponent + (d.weight.natAbs : ℂ) / 2)

private def secondPosition (d : ComplexCharacterData) : RealCharacterData :=
  RealJacquetFrobenius.charData 0 (d.exponent - (d.weight.natAbs : ℂ) / 2)

private def positions : RealBlock → List RealBlock
  | .character d => [.character d]
  | .induced d => [.character (firstPosition d), .character (secondPosition d)]

/-- Replace each induced block by its two real position characters in order. -/
def expand (ds : List RealBlock) : List RealBlock := ds.flatMap positions

private theorem expand_cons (d : RealBlock) (ds : List RealBlock) :
    expand (d :: ds) = positions d ++ expand ds := rfl

private theorem expand_append (ds es : List RealBlock) :
    expand (ds ++ es) = expand ds ++ expand es :=
  List.flatMap_append

@[simp] theorem realRank_expand (ds : List RealBlock) : realRank (expand ds) = realRank ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [expand_cons, realRank_append, ih, realRank_cons]
    cases d <;> simp [positions, RealBlock.rank]

private theorem positionParity_val (k : ℕ) : (positionParity k).val = (k + 1) % 2 := by
  rw [positionParity, Fin.val_add]
  change (k % 2 + 1) % 2 = (k + 1) % 2
  omega

/-- Expansion preserves the characters used to define the principal series. -/
theorem realPositionCharacter_expand (ds : List RealBlock) (i : ℕ) (a : ℝˣ) :
    realPositionCharacter (expand ds) i a = realPositionCharacter ds i a := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
    rw [expand_cons]
    cases d with
    | character d =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
    | induced d =>
      rcases i with _ | _ | i
      · change RealJacquetFrobenius.charFun (positionParity d.weight.natAbs)
          (d.exponent + (d.weight.natAbs : ℂ) / 2) a = realInducedFirstCharacter d a
        rw [RealJacquetFrobenius.charFun, realInducedFirstCharacter, positionParity_val,
          ← RealBlockPosition.sign_pow_eq_pow_mod_two a.ne_zero (d.weight.natAbs + 1)]
      · simp [positions, secondPosition, realPositionCharacter, realInducedSecondCharacter,
          RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun]
      · exact ih i

private def blockRatio (d : RealBlock) (s : ℂ) : ℂ :=
  (d.standardEpsilon : ℂ)⁻¹ * (RealLocalJacquet.dualBlock d).lFactor.denominator (1 - s) /
    d.lFactor.denominator s

private def inverseRatio (ds : List RealBlock) (s : ℂ) : ℂ :=
  (realStandardEpsilon ds : ℂ)⁻¹ *
    (realLFactor (ds.map RealLocalJacquet.dualBlock)).denominator (1 - s) /
    (realLFactor ds).denominator s

private theorem inverseRatio_append (ds es : List RealBlock) (s : ℂ) :
    inverseRatio (ds ++ es) s = inverseRatio ds s * inverseRatio es s := by
  simp only [inverseRatio, List.map_append, realLFactor_append, ReciprocalEntire.denominator_mul,
    realStandardEpsilon, List.prod_append, Units.val_mul, mul_inv, ← mul_div_mul_comm]
  congr 1
  ac_rfl

@[simp] private theorem inverseRatio_nil (s : ℂ) : inverseRatio [] s = 1 := by
  simp [inverseRatio, realStandardEpsilon, ReciprocalEntire.one]

@[simp] private theorem inverseRatio_singleton (d : RealBlock) (s : ℂ) :
    inverseRatio [d] s = blockRatio d s := by
  simp [inverseRatio, blockRatio, realStandardEpsilon]

private theorem inverseRatio_cons (d : RealBlock) (ds : List RealBlock) (s : ℂ) :
    inverseRatio (d :: ds) s = blockRatio d s * inverseRatio ds s := by
  change inverseRatio ([d] ++ ds) s = _
  rw [inverseRatio_append, inverseRatio_singleton]

private theorem inverseRatio_flatMap (ds : List RealBlock) (f : RealBlock → List RealBlock)
    (s : ℂ) : inverseRatio (ds.flatMap f) s = (ds.map fun d => inverseRatio (f d) s).prod := by
  induction ds with
  | nil => simp
  | cons d ds ih => rw [List.flatMap_cons, inverseRatio_append, ih, List.map_cons, List.prod_cons]

private theorem inv_I_pow (n : ℕ) : (Complex.I ^ n)⁻¹ = (-Complex.I) ^ n := by
  rw [← inv_pow]
  exact congrArg (fun z : ℂ => z ^ n) (RCLike.inv_I (K := ℂ))

private theorem blockRatio_character (d : RealCharacterData) (s : ℂ) :
    blockRatio (.character d) s = characterRatio d.parity (s + d.exponent) := by
  change (Complex.I ^ d.parity.val)⁻¹ *
    gammaReal.denominator (1 - s + (-d.exponent + (d.parity.val : ℂ))) /
    gammaReal.denominator (s + (d.exponent + (d.parity.val : ℂ))) = _
  rw [inv_I_pow, characterRatio]
  ring_nf

private theorem blockRatio_induced (d : ComplexCharacterData) (s : ℂ) :
    blockRatio (.induced d) s = inducedRatio d.weight.natAbs (s + d.exponent) := by
  change (Complex.I ^ (d.weight.natAbs + 1))⁻¹ *
    gammaComplex.denominator (1 - s + (-d.exponent + ((-d.weight).natAbs : ℂ) / 2)) /
    gammaComplex.denominator (s + (d.exponent + (d.weight.natAbs : ℂ) / 2)) = _
  rw [inv_I_pow, Int.natAbs_neg, inducedRatio]
  ring_nf

private theorem characterRatio_twist (k : ℕ) (q : Fin 2) (z : ℂ)
    (h₁ : gammaComplex.denominator (z + (k : ℂ) / 2) ≠ 0)
    (h₂ : gammaComplex.denominator (z - (k : ℂ) / 2) ≠ 0) :
    characterRatio (positionParity k + q) (z + (k : ℂ) / 2) *
      characterRatio q (z - (k : ℂ) / 2) = inducedRatio k z := by
  apply characterRatio_mul_eq_induced k _ q _ _ h₁ h₂
  rw [add_right_comm, positionParity_add, add_comm]

private theorem denominator_codiscrete (F : ReciprocalEntire) :
    ∀ᶠ s in Filter.codiscrete ℂ, F.denominator s ≠ 0 :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr F.denominator_eventually_ne_zero

private theorem complexDenominator_codiscrete (b : ℂ) :
    ∀ᶠ s in Filter.codiscrete ℂ, gammaComplex.denominator (s + b) ≠ 0 :=
  denominator_codiscrete (gammaComplex.shift b)

private theorem pairRatio_append_left (ds es fs : List RealBlock) (s : ℂ) :
    inverseRatio (realPairBlocks (ds ++ es) fs) s =
      inverseRatio (realPairBlocks ds fs) s * inverseRatio (realPairBlocks es fs) s := by
  simp only [realPairBlocks, List.flatMap_append, inverseRatio_append]

private theorem pairRatio_append_right (ds es fs : List RealBlock) (s : ℂ) :
    inverseRatio (realPairBlocks ds (es ++ fs)) s =
      inverseRatio (realPairBlocks ds es) s * inverseRatio (realPairBlocks ds fs) s := by
  simp only [realPairBlocks, inverseRatio_flatMap, List.flatMap_append, inverseRatio_append,
    List.prod_map_mul]

private theorem characterRatio_mul (c b : RealCharacterData) (s : ℂ) :
    blockRatio (.character (c.mul b)) s =
      characterRatio (c.parity + b.parity) (s + (c.exponent + b.exponent)) :=
  blockRatio_character (c.mul b) s

private theorem mixedRatio (d : ComplexCharacterData) (c : RealCharacterData) :
    ∀ᶠ s in Filter.codiscrete ℂ,
      blockRatio (.character ((firstPosition d).mul c)) s *
          blockRatio (.character ((secondPosition d).mul c)) s =
        blockRatio (.induced (d.twistReal c)) s := by
  let b := d.exponent + c.exponent
  let k := d.weight.natAbs
  filter_upwards [complexDenominator_codiscrete (b + (k : ℂ) / 2),
    complexDenominator_codiscrete (b - (k : ℂ) / 2)] with s h₁ h₂
  rw [characterRatio_mul, characterRatio_mul, blockRatio_induced]
  have h := characterRatio_twist k c.parity (s + b)
    (by simpa only [add_assoc] using h₁)
    (by simpa only [sub_eq_add_neg, add_assoc] using h₂)
  change characterRatio (positionParity k + c.parity)
      (s + (d.exponent + (k : ℂ) / 2 + c.exponent)) *
    characterRatio (0 + c.parity) (s + (d.exponent - (k : ℂ) / 2 + c.exponent)) =
      inducedRatio k (s + b)
  rw [zero_add, show s + (d.exponent + (k : ℂ) / 2 + c.exponent) =
    s + b + (k : ℂ) / 2 by dsimp [b]; ring,
    show s + (d.exponent - (k : ℂ) / 2 + c.exponent) =
      s + b - (k : ℂ) / 2 by dsimp [b]; ring]
  exact h

private theorem blockRatio_mul_character_comm (c b : RealCharacterData) (s : ℂ) :
    blockRatio (.character (c.mul b)) s = blockRatio (.character (b.mul c)) s := by
  rw [characterRatio_mul, characterRatio_mul, add_comm c.parity, add_comm c.exponent]

private theorem inducedRatio_add_sub (p q : ℤ) (z : ℂ) :
    inducedRatio (p + q).natAbs z * inducedRatio (p - q).natAbs z =
      inducedRatio (p.natAbs + q.natAbs) z *
        inducedRatio (max p.natAbs q.natAbs - min p.natAbs q.natAbs) z := by
  have h :
      ((p + q).natAbs = p.natAbs + q.natAbs ∧
        (p - q).natAbs = max p.natAbs q.natAbs - min p.natAbs q.natAbs) ∨
      ((p - q).natAbs = p.natAbs + q.natAbs ∧
        (p + q).natAbs = max p.natAbs q.natAbs - min p.natAbs q.natAbs) := by
    rcases le_total q.natAbs p.natAbs with h | h
    · rw [max_eq_left h, min_eq_right h]
      omega
    · rw [max_eq_right h, min_eq_left h]
      omega
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]
  · rw [hp, hq, mul_comm]

private theorem characterRatio_tensor_unordered (m n : ℕ) (z : ℂ)
    (hpp : gammaComplex.denominator (z + ((m : ℂ) + (n : ℂ)) / 2) ≠ 0)
    (hpm : gammaComplex.denominator (z + ((m : ℂ) - (n : ℂ)) / 2) ≠ 0)
    (hmp : gammaComplex.denominator (z - ((m : ℂ) - (n : ℂ)) / 2) ≠ 0)
    (hmm : gammaComplex.denominator (z - ((m : ℂ) + (n : ℂ)) / 2) ≠ 0) :
    characterRatio (positionParity m + positionParity n) (z + ((m : ℂ) + (n : ℂ)) / 2) *
        characterRatio (positionParity m) (z + ((m : ℂ) - (n : ℂ)) / 2) *
        characterRatio (positionParity n) (z - ((m : ℂ) - (n : ℂ)) / 2) *
        characterRatio 0 (z - ((m : ℂ) + (n : ℂ)) / 2) =
      inducedRatio (m + n) z * inducedRatio (max m n - min m n) z := by
  rcases le_total n m with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact characterRatio_tensor m n h z hpp hpm hmp hmm
  · rw [max_eq_right h, min_eq_left h]
    have hpn : z + ((n : ℂ) - (m : ℂ)) / 2 = z - ((m : ℂ) - (n : ℂ)) / 2 := by ring
    have hmn : z - ((n : ℂ) - (m : ℂ)) / 2 = z + ((m : ℂ) - (n : ℂ)) / 2 := by ring
    have he := characterRatio_tensor n m h z
      (by simpa only [add_comm (n : ℂ) (m : ℂ)] using hpp)
      (hpn ▸ hmp) (hmn ▸ hpm) (by simpa only [add_comm (n : ℂ) (m : ℂ)] using hmm)
    rw [hpn, hmn, add_comm (n : ℂ) (m : ℂ), add_comm (positionParity n) (positionParity m),
      Nat.add_comm n m, mul_right_comm
        (characterRatio (positionParity m + positionParity n) _)] at he
    exact he

private theorem inducedTensorRatio (d e : ComplexCharacterData) :
    ∀ᶠ s in Filter.codiscrete ℂ,
      blockRatio (.character ((firstPosition d).mul (firstPosition e))) s *
        blockRatio (.character ((firstPosition d).mul (secondPosition e))) s *
        blockRatio (.character ((secondPosition d).mul (firstPosition e))) s *
        blockRatio (.character ((secondPosition d).mul (secondPosition e))) s =
      blockRatio (.induced (d.mul e)) s * blockRatio (.induced (d.mul e.conj)) s := by
  let b := d.exponent + e.exponent
  let m := d.weight.natAbs
  let n := e.weight.natAbs
  filter_upwards [complexDenominator_codiscrete (b + ((m : ℂ) + (n : ℂ)) / 2),
    complexDenominator_codiscrete (b + ((m : ℂ) - (n : ℂ)) / 2),
    complexDenominator_codiscrete (b - ((m : ℂ) - (n : ℂ)) / 2),
    complexDenominator_codiscrete (b - ((m : ℂ) + (n : ℂ)) / 2)] with s hpp hpm hmp hmm
  simp only [characterRatio_mul, blockRatio_induced, firstPosition, secondPosition,
    RealJacquetFrobenius.charData, ComplexCharacterData.mul, ComplexCharacterData.conj,
    add_zero, zero_add, ← sub_eq_add_neg]
  rw [inducedRatio_add_sub]
  have h := characterRatio_tensor_unordered m n (s + b)
    (by simpa only [add_assoc] using hpp) (by simpa only [add_assoc] using hpm)
    (by simpa only [sub_eq_add_neg, add_assoc] using hmp)
    (by simpa only [sub_eq_add_neg, add_assoc] using hmm)
  dsimp [b, m, n] at h
  ring_nf at h ⊢
  exact h

private theorem pairRatio_expand_singletons (d e : RealBlock) :
    ∀ᶠ s in Filter.codiscrete ℂ,
      inverseRatio (realPairBlocks (expand [d]) (expand [e])) s =
        inverseRatio (realPairBlocks [d] [e]) s := by
  cases d with
  | character c =>
    cases e with
    | character b => exact Filter.Eventually.of_forall (fun _ => rfl)
    | induced e =>
      filter_upwards [mixedRatio e c] with s hs
      change inverseRatio [.character (c.mul (firstPosition e)),
        .character (c.mul (secondPosition e))] s =
          inverseRatio [.induced (e.twistReal c)] s
      simp only [inverseRatio_cons, inverseRatio_nil, mul_one, blockRatio_mul_character_comm c]
      exact hs
  | induced d =>
    cases e with
    | character b =>
      filter_upwards [mixedRatio d b] with s hs
      change inverseRatio [.character ((firstPosition d).mul b),
        .character ((secondPosition d).mul b)] s =
          inverseRatio [.induced (d.twistReal b)] s
      simp only [inverseRatio_cons, inverseRatio_nil, mul_one]
      exact hs
    | induced e =>
      filter_upwards [inducedTensorRatio d e] with s hs
      change inverseRatio [.character ((firstPosition d).mul (firstPosition e)),
        .character ((firstPosition d).mul (secondPosition e)),
        .character ((secondPosition d).mul (firstPosition e)),
        .character ((secondPosition d).mul (secondPosition e))] s =
          inverseRatio [.induced (d.mul e), .induced (d.mul e.conj)] s
      simp only [inverseRatio_cons, inverseRatio_nil, mul_one]
      simpa only [mul_assoc] using hs

private theorem pairRatio_expand (ds es : List RealBlock) :
    ∀ᶠ s in Filter.codiscrete ℂ,
      inverseRatio (realPairBlocks (expand ds) (expand es)) s =
        inverseRatio (realPairBlocks ds es) s := by
  induction ds with
  | nil => exact Filter.Eventually.of_forall (fun _ => rfl)
  | cons d ds ih =>
    have h : ∀ᶠ s in Filter.codiscrete ℂ,
        inverseRatio (realPairBlocks (expand [d]) (expand es)) s =
          inverseRatio (realPairBlocks [d] es) s := by
      clear ih
      induction es with
      | nil =>
        have hp (fs : List RealBlock) : realPairBlocks fs [] = [] := by simp [realPairBlocks]
        exact Filter.Eventually.of_forall (fun s => by rw [show expand [] = [] from rfl, hp, hp])
      | cons e es ies =>
        filter_upwards [pairRatio_expand_singletons d e, ies] with s hde hes
        change inverseRatio (realPairBlocks (expand [d]) (expand ([e] ++ es))) s =
          inverseRatio (realPairBlocks [d] ([e] ++ es)) s
        rw [expand_append, pairRatio_append_right, pairRatio_append_right, hde, hes]
    filter_upwards [h, ih] with s hd hds
    change inverseRatio (realPairBlocks (expand ([d] ++ ds)) (expand es)) s =
      inverseRatio (realPairBlocks ([d] ++ ds) es) s
    rw [expand_append, pairRatio_append_left, pairRatio_append_left, hd, hds]

private theorem gammaBlocks_tensor_dual (d e : RealBlock) :
    ((RealLocalJacquet.dualBlock d).tensor (RealLocalJacquet.dualBlock e)).map
        RealBlock.gammaBlock =
      (d.tensor e).map (fun b => (RealLocalJacquet.dualBlock b).gammaBlock) := by
  cases d <;> cases e <;>
    simp [RealBlock.tensor, RealBlock.gammaBlock, RealLocalJacquet.dualBlock,
      RealCharacterData.mul, RealCharacterData.inverse, ComplexCharacterData.mul,
      ComplexCharacterData.inverse, ComplexCharacterData.conj, ComplexCharacterData.twistReal,
      add_comm, neg_neg]

private theorem dualPairLFactor_eq (ds es : List RealBlock) :
    realPairLFactor (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) =
      realLFactor ((realPairBlocks ds es).map RealLocalJacquet.dualBlock) := by
  rw [realPairLFactor, realLFactor_eq_gammaProduct, realLFactor_eq_gammaProduct]
  congr 1
  simp only [realPairBlocks, List.map_flatMap, List.flatMap_map, List.map_map]
  apply congrArg (fun f => ds.flatMap f)
  funext d
  apply congrArg (fun f => es.flatMap f)
  funext e
  exact gammaBlocks_tensor_dual d e

private theorem determinant_positions (d : RealBlock) (a : ℝˣ) :
    RealJacquet.determinant (positions d) a = d.determinant a := by
  cases d with
  | character d => simp [positions, RealJacquet.determinant]
  | induced d =>
    have habs : ((|(a : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr a.ne_zero
    have hsign : (realSign a : ℂ)⁻¹ = (realSign a : ℂ) := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [Units.val_pow_eq_pow_val, pow_two, Units.val_mul, Units.val_one] using
        congrArg (fun z : ℂˣ => (z : ℂ)) (RealJacquet.realSign_sq a)
    have hpow : (realSign a : ℂ) ^ d.weight = (realSign a : ℂ) ^ d.weight.natAbs := by
      by_cases h : 0 ≤ d.weight
      · rw [← zpow_natCast, show (d.weight.natAbs : ℤ) = d.weight by omega]
      · rw [← zpow_natCast, show (d.weight.natAbs : ℤ) = -d.weight by omega, ← inv_zpow', hsign]
    apply Units.ext
    simp only [positions, RealJacquet.determinant, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, Units.val_mul, RealBlock.coe_determinant_character,
      firstPosition, secondPosition]
    rw [RealJacquetFrobenius.charData_character_apply,
      RealJacquetFrobenius.charData_character_apply, RealBlock.coe_determinant_induced,
      d.character_eq]
    simp only [RealJacquetFrobenius.charFun, positionParity_val, Fin.val_zero, pow_zero,
      one_mul, show (realToComplex a : ℂ) = (a : ℝ) from rfl, Complex.norm_real,
      Real.norm_eq_abs, ← Complex.ofReal_div]
    rw [← RealBlockPosition.sign_pow_eq_pow_mod_two a.ne_zero (d.weight.natAbs + 1),
      mul_assoc, ← Complex.cpow_add _ _ habs,
      show d.exponent + (d.weight.natAbs : ℂ) / 2 + (d.exponent - (d.weight.natAbs : ℂ) / 2) =
        2 * d.exponent by ring, ← coe_realSign, hpow, pow_succ]
    ac_rfl

/-- The determinant of the inducing positions is the determinant of the block presentation. -/
theorem determinant_expand (ds : List RealBlock) (a : ℝˣ) :
    RealJacquet.determinant (expand ds) a = RealJacquet.determinant ds a := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [expand_cons, RealJacquet.determinant_append, determinant_positions, ih]
    rfl

/-- The local pair multiplier after clearing the primal reciprocal L-factor.
The two dual lists consist of the inverses of the displayed primal blocks. -/
def pairMultiplier (ds es : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) : ℂ :=
  (realPairEpsilon ds es a c hc s : ℂ) * (realPairLFactor ds es).denominator s /
    (realPairLFactor (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock)).denominator (1 - s)

private theorem coe_list_prod (ds : List RealBlock) (f : RealBlock → ℂˣ) :
    ((ds.map f).prod : ℂ) = (ds.map fun d => (f d : ℂ)).prod := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]

private theorem pairMultiplier_eq (ds es : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    pairMultiplier ds es a c hc s =
      (c : ℂ) ^ realRank (realPairBlocks ds es) *
        (RealJacquet.determinant (realPairBlocks ds es) a : ℂ) *
        ((|(a : ℝ)| : ℝ) : ℂ) ^ ((realRank (realPairBlocks ds es) : ℂ) * (s - 1)) *
        (inverseRatio (realPairBlocks ds es) s)⁻¹ := by
  rw [pairMultiplier, dualPairLFactor_eq, realPairEpsilon, coe_realEpsilon,
    ← coe_list_prod, ← coe_list_prod]
  simp only [inverseRatio, RealJacquet.determinant, realPairLFactor, realStandardEpsilon,
    mul_inv, inv_inv, div_eq_mul_inv]
  ac_rfl

/-- Expanding both presentations preserves the pair Gamma multiplier off a discrete set,
for any real additive parameter and positive Haar scale. -/
def PairMultiplierExpansionStatement : Prop :=
  ∀ (ds es : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c),
    ∀ᶠ s in Filter.codiscrete ℂ,
      pairMultiplier (expand ds) (expand es) a c hc s = pairMultiplier ds es a c hc s

theorem pairMultiplier_expand : PairMultiplierExpansionStatement := by
  intro ds es a c hc
  filter_upwards [pairRatio_expand ds es] with s hs
  simp only [pairMultiplier_eq, realRank_realPairBlocks, RealJacquet.determinant_realPairBlocks,
    realRank_expand, determinant_expand, hs]

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
