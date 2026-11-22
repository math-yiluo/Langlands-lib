import Langlands.Global.RankinSelberg.RealParameterDeterminant
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-! # Real pair factors of an adjoined character with a shifted exponent -/

noncomputable section

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)

/-! ### Adjoining one block -/

/-- The pair `L`-factor of an adjoined block is the product of the singleton and the
remaining factors. -/
theorem realPairLFactor_cons_mul (d : RealBlock) (ds es : List RealBlock) :
    realPairLFactor (d :: ds) es = (realPairLFactor [d] es).mul (realPairLFactor ds es) := by
  simpa only [realPairLFactor, realPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using realLFactor_append (es.flatMap d.tensor) (realPairBlocks ds es)

/-- The pair `ε`-factor of an adjoined block is the product of the singleton and the
remaining factors. -/
theorem realPairEpsilon_cons_mul (d : RealBlock) (ds es : List RealBlock)
    (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    realPairEpsilon (d :: ds) es a c hc s =
      realPairEpsilon [d] es a c hc s * realPairEpsilon ds es a c hc s := by
  simpa only [realPairEpsilon, realPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using realEpsilon_append (es.flatMap d.tensor) (realPairBlocks ds es) a c hc s

/-! ### Shifting the exponent of the adjoined character -/

theorem realPairBlocks_singleton_character (c : RealCharacterData) (fs : List RealCharacterData) :
    realPairBlocks [RealBlock.character c] (fs.map RealBlock.character) =
      fs.map fun f => RealBlock.character (c.mul f) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [realPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_cons] at ih ⊢
    rw [ih]
    rfl

/-- Raising the exponent of the adjoined character by `z` shifts the pair `L`-factor
against a character list by `z`. -/
theorem realPairLFactor_character_shift {c c' : RealCharacterData} {z : ℂ}
    (hp : c.parity = c'.parity) (he : c.exponent = c'.exponent + z)
    (fs : List RealCharacterData) (s : ℂ) :
    (realPairLFactor [RealBlock.character c] (fs.map RealBlock.character)).denominator s =
      (realPairLFactor [RealBlock.character c'] (fs.map RealBlock.character)).denominator
        (s + z) := by
  rw [realPairLFactor, realPairLFactor, realPairBlocks_singleton_character,
    realPairBlocks_singleton_character, denominator_realLFactor, denominator_realLFactor,
    List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro f _
  simp only [Function.comp_apply, RealBlock.lFactor_character,
    ReciprocalEntire.denominator_shift]
  congr 1
  change s + ((c.exponent + f.exponent) + ((c.parity + f.parity).val : ℂ)) =
    (s + z) + ((c'.exponent + f.exponent) + ((c'.parity + f.parity).val : ℂ))
  rw [hp, he]
  ring

/-- Raising the exponent of the adjoined character by `z` shifts the pair `ε`-factor
against a character list by `z`. -/
theorem realPairEpsilon_character_shift {c c' : RealCharacterData} {z : ℂ}
    (hp : c.parity = c'.parity) (he : c.exponent = c'.exponent + z)
    (fs : List RealCharacterData) (b : ℝˣ) (k : NNReal) (hk : 0 < k) (s : ℂ) :
    (realPairEpsilon [RealBlock.character c] (fs.map RealBlock.character) b k hk s : ℂ) =
      (realPairEpsilon [RealBlock.character c'] (fs.map RealBlock.character) b k hk (s + z) :
        ℂ) := by
  rw [realPairEpsilon, realPairEpsilon, realPairBlocks_singleton_character,
    realPairBlocks_singleton_character]
  have key : ∀ f ∈ fs, (RealBlock.character (c.mul f)).epsilon b k hk s =
      (RealBlock.character (c'.mul f)).epsilon b k hk (s + z) := by
    intro f _
    apply Units.ext
    change (((c.mul f).epsilon b k hk s : ℂˣ) : ℂ) = (((c'.mul f).epsilon b k hk (s + z) : ℂˣ) : ℂ)
    have hne : ((|(b : ℝ)| : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr b.ne_zero)
    rw [RealCharacterData.coe_epsilon, RealCharacterData.coe_epsilon, (c.mul f).character_eq,
      (c'.mul f).character_eq]
    change (k : ℂ) * ((((b : ℝ) / |(b : ℝ)| : ℝ) : ℂ) ^ (c.parity + f.parity).val *
        ((|(b : ℝ)| : ℝ) : ℂ) ^ (c.exponent + f.exponent)) * ((|(b : ℝ)| : ℝ) : ℂ) ^ (s - 1) *
        Complex.I ^ (c.parity + f.parity).val =
      (k : ℂ) * ((((b : ℝ) / |(b : ℝ)| : ℝ) : ℂ) ^ (c'.parity + f.parity).val *
        ((|(b : ℝ)| : ℝ) : ℂ) ^ (c'.exponent + f.exponent)) * ((|(b : ℝ)| : ℝ) : ℂ) ^ (s + z - 1) *
        Complex.I ^ (c'.parity + f.parity).val
    rw [hp, he]
    have hX : ((|(b : ℝ)| : ℝ) : ℂ) ^ (c'.exponent + z + f.exponent) *
        ((|(b : ℝ)| : ℝ) : ℂ) ^ (s - 1) =
        ((|(b : ℝ)| : ℝ) : ℂ) ^ (c'.exponent + f.exponent) *
        ((|(b : ℝ)| : ℝ) : ℂ) ^ (s + z - 1) := by
      rw [← Complex.cpow_add _ _ hne, ← Complex.cpow_add _ _ hne]
      ring_nf
    linear_combination ((k : ℂ) * (((b : ℝ) / |(b : ℝ)| : ℝ) : ℂ) ^ (c'.parity + f.parity).val *
      Complex.I ^ (c'.parity + f.parity).val) * hX
  congr 1
  simp only [realEpsilon, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun f hf => key f hf)

/-- The characters `charData p z` and `charData p 0` differ only by the exponent `z`. -/
theorem realPairLFactor_charData_shift (p : Fin 2) (z : ℂ) (fs : List RealCharacterData) (s : ℂ) :
    (realPairLFactor [RealBlock.character (charData p z)] (fs.map RealBlock.character)).denominator
        s =
      (realPairLFactor [RealBlock.character (charData p 0)]
        (fs.map RealBlock.character)).denominator (s + z) :=
  realPairLFactor_character_shift (c := charData p z) (c' := charData p 0) rfl (zero_add z).symm fs s

theorem realPairEpsilon_charData_shift (p : Fin 2) (z : ℂ) (fs : List RealCharacterData)
    (b : ℝˣ) (k : NNReal) (hk : 0 < k) (s : ℂ) :
    (realPairEpsilon [RealBlock.character (charData p z)] (fs.map RealBlock.character) b k hk s :
        ℂ) =
      (realPairEpsilon [RealBlock.character (charData p 0)] (fs.map RealBlock.character) b k hk
        (s + z) : ℂ) :=
  realPairEpsilon_character_shift (c := charData p z) (c' := charData p 0) rfl (zero_add z).symm fs
    b k hk s

/-- The product of the corank-one and shifted matrix denominators in the equal-rank
unfolding is the pair denominator of the adjoined list. -/
theorem realPairLFactor_equal_pair (p : Fin 2) (z : ℂ) (ds : List RealBlock)
    (fs : List RealCharacterData) (s : ℂ) :
    (realPairLFactor (fs.map RealBlock.character) ds).denominator s *
        (realPairLFactor [RealBlock.character (charData p 0)]
          (fs.map RealBlock.character)).denominator (s + z) =
      (realPairLFactor (RealBlock.character (charData p z) :: ds)
        (fs.map RealBlock.character)).denominator s := by
  rw [realPairLFactor_cons_mul (RealBlock.character (charData p z)) ds (fs.map RealBlock.character),
    ReciprocalEntire.denominator_mul, realPairLFactor_charData_shift p z fs s, CuspidalPairPartialGammaGlobal.realPairLFactor_denominator_comm
      (fs.map RealBlock.character) ds, mul_comm]

/-! ### Duals -/

/-- The inverse of `charData p z` is `charData p (-z)`. -/
theorem inverse_charData_eq (p : Fin 2) (z : ℂ) : (charData p z).inverse = charData p (-z) := by
  have h : (charData p z).inverse.character = (charData p (-z)).character := by
    ext x
    exact ((charData p z).inverse.character_eq x).trans ((charData p (-z)).character_eq x).symm
  change RealCharacterData.mk (charData p z).inverse.character p (-z) _ =
    RealCharacterData.mk (charData p (-z)).character p (-z) _
  congr 1

theorem dualBlock_charData (p : Fin 2) (z : ℂ) :
    RealLocalJacquet.dualBlock (RealBlock.character (charData p z)) =
      RealBlock.character (charData p (-z)) :=
  congrArg RealBlock.character (inverse_charData_eq p z)

theorem map_dualBlock_character (fs : List RealCharacterData) :
    (fs.map RealBlock.character).map RealLocalJacquet.dualBlock =
      (fs.map RealCharacterData.inverse).map RealBlock.character := by
  simp only [List.map_map]
  rfl

/-! ### The equal-rank sign -/

private theorem determinant_cons_mul (d : RealBlock) (ds : List RealBlock) (a : ℝˣ) :
    determinant (d :: ds) a = d.determinant a * determinant ds a := rfl

private theorem block_determinant_one' (d : RealBlock) : d.determinant 1 = 1 := by
  cases d with
  | character d => exact map_one d.character
  | induced d =>
    have h : realToComplex 1 = 1 := map_one (Units.map Complex.ofRealHom.toMonoidHom)
    have hsign : realSign 1 = 1 := by
      apply Units.ext
      simp [coe_realSign]
    simp [RealBlock.determinant, ComplexCharacterData.realInducedDeterminant, h, hsign]

/-- The value at `-1` of the determinant character of a block list squares to one. -/
theorem determinant_minusOne_sq' (ds : List RealBlock) :
    (determinant ds (-1) : ℂ) ^ 2 = 1 := by
  induction ds with
  | nil => simp [determinant]
  | cons d ds ih =>
    have hd := block_determinant_neg d (-1)
    rw [neg_neg, block_determinant_one', ← pow_two] at hd
    have hd' := congrArg (fun z : ℂˣ => (z : ℂ)) hd.symm
    rw [Units.val_pow_eq_pow_val, Units.val_one] at hd'
    rw [determinant_cons_mul, Units.val_mul, mul_pow, hd', ih, one_mul]

/-- The sign and `ε`-factor bookkeeping of the equal-rank step: the corank-one equation at
parameter `a` with its sign, the matrix equation at `-a`, and the Weyl sign
`d(-1)^(r+1)` combine to the equal-rank sign and `ε`-factor of the adjoined list at `-a`. -/
theorem equal_epsilon_coefficient {r : ℕ} (d : RealCharacterData) (ds es : List RealBlock)
    (hd : realRank ds = r + 1) (he : realRank es = r + 2)
    (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) :
    (d.character (-1) : ℂ) ^ (r + 1) *
      ((((determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ)) *
          (realPairEpsilon ds es a c hc s : ℂ)) *
        (realPairEpsilon [.character d] es (-a) c hc s : ℂ)) =
    (determinant (.character d :: ds) (-1) : ℂ) ^ (r + 1) *
      (realPairEpsilon (.character d :: ds) es (-a) c hc s : ℂ) := by
  have hflip := pair_epsilon_neg ds es (-a) c hc s
  rw [neg_neg, determinant_realPairBlocks, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, hd, he] at hflip
  have hsign := unequal_sign _ _ (determinant_minusOne_sq' es) (determinant_minusOne_sq' ds) (r + 1) r
  rw [hflip, realPairEpsilon_cons_mul (.character d) ds es (-a) c hc s,
    Units.val_mul, determinant_cons_mul, Units.val_mul, mul_pow]
  change _ = ((d.character (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ) ^ (r + 1)) * _
  calc
    _ = (d.character (-1) : ℂ) ^ (r + 1) *
        (((determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ)) *
          ((determinant es (-1) : ℂ) ^ (r + 1) * (determinant ds (-1) : ℂ) ^ (r + 2))) *
        ((realPairEpsilon [.character d] es (-a) c hc s : ℂ) *
          (realPairEpsilon ds es (-a) c hc s : ℂ)) := by ring
    _ = _ := by rw [hsign]

/-! ### Summary statement -/

/-- Adjoining the real character `charData p z` to a block list `ds`: the corank-one pair
denominator at `s` times the matrix denominator of `charData p 0` at `s + z` is the pair
denominator of the adjoined list at `s`, and the singleton `ε`-factor of `charData p z` at `s`
is that of `charData p 0` at `s + z`, against any character list. -/
def RealLocalEqualNormalizedFactorsStatement : Prop :=
  ∀ (p : Fin 2) (z : ℂ) (ds : List RealBlock) (fs : List RealCharacterData) (b : ℝˣ)
    (k : NNReal) (hk : 0 < k) (s : ℂ),
    (realPairLFactor (fs.map RealBlock.character) ds).denominator s *
        (realPairLFactor [RealBlock.character (charData p 0)]
          (fs.map RealBlock.character)).denominator (s + z) =
      (realPairLFactor (RealBlock.character (charData p z) :: ds)
        (fs.map RealBlock.character)).denominator s ∧
    (realPairEpsilon [RealBlock.character (charData p z)] (fs.map RealBlock.character) b k hk s :
        ℂ) =
      (realPairEpsilon [RealBlock.character (charData p 0)] (fs.map RealBlock.character) b k hk
        (s + z) : ℂ)

theorem realLocalEqualNormalizedFactors : RealLocalEqualNormalizedFactorsStatement :=
  fun p z ds fs b k hk s =>
    ⟨realPairLFactor_equal_pair p z ds fs s, realPairEpsilon_charData_shift p z fs b k hk s⟩

end Langlands.Global.RankinSelbergGlobal.RealJacquet
