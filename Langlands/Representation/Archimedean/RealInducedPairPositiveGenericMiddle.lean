import Langlands.Representation.Archimedean.RealAdjacentFourierBand
import Langlands.Representation.Archimedean.RealInducedPairPositiveCrossedQuotient
import Langlands.Representation.Archimedean.RealInducedPairPositiveOppositeOuter
import Langlands.Representation.Archimedean.RealIntegralGenericPolynomial

/-! # The invertible middle polynomial in the flipped positive presentation -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairPositiveGenericMiddle

open Langlands.LocalFactor.Archimedean RealStandardFiltration
open RealInducedPairLinkedReplacement RealInducedPairCrossedReplacement
open RealBlockJacquet RealBlockFrobeniusMap RealCharacterPair RealCharacterPairReducible
open RealTailMultiplierPolynomial RealBlockMultiplier RealBlockFourierFinite
open RealBlockFrobeniusDisjoint RealAdjacentFourierBand
open Polynomial (eval)

namespace P
export RealInducedPairQuotientPresentation
  (lo hi X quotientMap quotientSection quotient_section pair_parity
    Dd De dataDd dataDe dataDeX KF_Z qd qe dataQd dataQe ker_quotient)
end P

namespace C
export RealInducedPairPositiveCrossedQuotient
  (source cutoff cutoff_pos crossed_cutoffs crossedLeftParity crossed_lower_pos crossed_upper_pos
    crossedQuotient beforeDescent_apply quotient middleTail middleTailData middle_parity
    middle_sign binomial_low inclusion_coe)
end C

namespace M
export RealInducedPairCrossedMiddleQuotient
  (leftParity rightParity crossed_leftParity inclusion)
end M

open RealInducedPairPositiveOppositeOuter (flipParity)

variable {d e : ComplexCharacterData} {k : ℕ}

/-- Flip the parities of the two characters presenting the first induction
block and retain the parities of the second pair. -/
abbrev source (d e : ComplexCharacterData) (k : ℕ) :=
  P.X d e (flipParity (M.leftParity d)) (M.rightParity d e k)

abbrev leftLower (d : ComplexCharacterData) := P.lo d (flipParity (M.leftParity d))
abbrev leftUpper (d : ComplexCharacterData) := P.hi d (flipParity (M.leftParity d))
abbrev rightLower (d e : ComplexCharacterData) (k : ℕ) := P.lo e (M.rightParity d e k)
abbrev rightUpper (d e : ComplexCharacterData) (k : ℕ) := P.hi e (M.rightParity d e k)

abbrev swapped (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.character (leftLower d), .character (rightLower d e k),
    .character (leftUpper d), .character (rightUpper d e k)]

abbrev crossed (d e : ComplexCharacterData) (k : ℕ) :=
  P.X (lowerData d e k) (upperData d e k) (flipParity (C.crossedLeftParity d e k)) 0

theorem swapped_eq_crossed (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    swapped d e k = crossed d e k := by
  let sd := flipParity (M.leftParity d)
  let se := M.rightParity d e k
  let s := flipParity (C.crossedLeftParity d e k)
  have hp : s = sd := congrArg flipParity (M.crossed_leftParity hd he hH)
  obtain ⟨hL, hR⟩ := C.crossed_cutoffs hH
  obtain ⟨hu, hx⟩ := lower_endpoints h sd se s
  obtain ⟨hv, hy⟩ := upper_endpoints h sd se 0
  have hu' : P.lo (lowerData d e k) s = leftLower d :=
    congrArg₂ RealJacquetFrobenius.charData hp hu
  have hx' : P.hi (lowerData d e k) s = rightLower d e k := by
    apply congrArg₂ RealJacquetFrobenius.charData _ hx
    apply Fin.ext
    change (s.val + (lowerData d e k).weight.natAbs + 1) % 2 = se.val
    rw [hp, hL]
    change ((d.weight.natAbs % 2 + 1) % 2 + (d.weight.natAbs + C.cutoff d e k) + 1) % 2 =
      C.cutoff d e k % 2
    omega
  have hv' : P.lo (upperData d e k) 0 = leftUpper d := by
    apply congrArg₂ RealJacquetFrobenius.charData _ hv
    apply Fin.ext
    dsimp [sd, flipParity, M.leftParity]
    omega
  have hy' : P.hi (upperData d e k) 0 = rightUpper d e k := by
    apply congrArg₂ RealJacquetFrobenius.charData _ hy
    apply Fin.ext
    change (0 + (upperData d e k).weight.natAbs + 1) % 2 =
      (se.val + e.weight.natAbs + 1) % 2
    rw [hR]
    change (0 + (e.weight.natAbs + C.cutoff d e k) + 1) % 2 =
      (C.cutoff d e k % 2 + e.weight.natAbs + 1) % 2
    omega
  change [RealBlock.character (leftLower d), RealBlock.character (rightLower d e k),
      RealBlock.character (leftUpper d), RealBlock.character (rightUpper d e k)] =
    [RealBlock.character (P.lo (lowerData d e k) s), RealBlock.character (P.hi (lowerData d e k) s),
      RealBlock.character (P.lo (upperData d e k) 0), RealBlock.character (P.hi (upperData d e k) 0)]
  rw [hu', hx', hv', hy']

abbrev parity (d e : ComplexCharacterData) (k : ℕ) :=
  pairParity (rightLower d e k) (leftUpper d)

theorem parity_eq (d e : ComplexCharacterData) (k : ℕ) :
    Even ((C.cutoff d e k : ℤ) - parity d e k) := by
  change Even ((C.cutoff d e k : ℤ) - (((C.cutoff d e k % 2 +
    (((d.weight.natAbs % 2 + 1) % 2 + d.weight.natAbs + 1) % 2)) % 2 : ℕ) : ℤ))
  rw [Int.even_iff]
  omega

private theorem polynomial_symmetry (d e : ComplexCharacterData) (k : ℕ) :
    RealBlockMultiplier.IsSymmetric (parity d e k) (sigma0 (rightLower d e k) (leftUpper d))
      (fun j : ℤ => (tailPolynomial (C.cutoff d e k)).eval (j : ℂ)) := by
  have hs := RealIntegralGenericPolynomial.parity_sign
    (pairParity_eq (rightLower d e k) (leftUpper d)) (parity_eq d e k)
  change RealBlockMultiplier.IsSymmetric (parity d e k) ((-1 : ℂ) ^ (parity d e k).natAbs)
    (fun j : ℤ => (tailPolynomial (C.cutoff d e k)).eval (j : ℂ))
  rw [← hs]
  exact RealIntegralGenericPolynomial.polynomial_symmetric _ _

theorem middleData (d e : ComplexCharacterData) (k : ℕ) :
    IsBlockFrobData 4 (source d e k) (swapped d e k) 1 (parity d e k)
      (sigma0 (rightLower d e k) (leftUpper d))
      (fun j : ℤ => (tailPolynomial (C.cutoff d e k)).eval (j : ℂ)) :=
  data_swap (n := 4) (pre := [.character (leftLower d)]) (post := [.character (rightUpper d e k)])
    rfl (polynomial_symmetry d e k)

theorem inverseData (d e : ComplexCharacterData) (k : ℕ) :
    IsBlockFrobData 4 (swapped d e k) (source d e k) 1 (parity d e k)
      (sigma0 (rightLower d e k) (leftUpper d))⁻¹
      (fun j : ℤ => ((tailPolynomial (C.cutoff d e k)).eval (j : ℂ))⁻¹) :=
  data_unswap (n := 4) (pre := [.character (leftLower d)]) (post := [.character (rightUpper d e k)])
    rfl (polynomial_symmetry d e k)

def middle (d e : ComplexCharacterData) (k : ℕ) : KF 4 (source d e k) →ₗ[ℂ] KF 4 (swapped d e k) :=
  blockFrobMap (middleData d e k)

def inverse (d e : ComplexCharacterData) (k : ℕ) : KF 4 (swapped d e k) →ₗ[ℂ] KF 4 (source d e k) :=
  blockFrobMap (inverseData d e k)

private theorem polynomial_nonzero_on_parity {j : ℤ}
    (hj : Even (j - parity d e k)) : (tailPolynomial (C.cutoff d e k)).eval (j : ℂ) ≠ 0 := by
  apply RealIntegralGenericPolynomial.polynomial_ne_zero
  have hc := parity_eq d e k
  rw [Int.even_iff] at hj hc ⊢
  omega

theorem inverse_middle (f : KF 4 (source d e k)) :
    inverse d e k (middle d e k f) = f := by
  apply blockFrobMap_blockFrobMap_eq (middleData d e k) (inverseData d e k) f
  intro j hj hbad
  exact (hbad (inv_mul_cancel₀ (polynomial_nonzero_on_parity hj))).elim

theorem middle_inverse (f : KF 4 (swapped d e k)) :
    middle d e k (inverse d e k f) = f := by
  apply blockFrobMap_blockFrobMap_eq (inverseData d e k) (middleData d e k) f
  intro j hj hbad
  exact (hbad (mul_inv_cancel₀ (polynomial_nonzero_on_parity hj))).elim

local notation "Φ" => blockFourierCoefficient
local notation "G₄" => Langlands.GeneralLinear 4 ℝ
local notation "K₄" => unitaryCompact ℝ 4

/-- The double coefficient on the two disjoint outer rotations. -/
abbrev doubleCoeff (i j : ℤ) (f : G₄ → ℂ) : G₄ → ℂ := Φ 4 2 j (Φ 4 0 i f)

private theorem outer_disjoint : (0 + 1 < (2 : ℕ)) ∨ 2 + 1 < 0 := Or.inl (by decide)

theorem doubleCoeff_sub {f g : G₄ → ℂ} (hf : Continuous f) (hg : Continuous g) (i j : ℤ) (x : G₄) :
    doubleCoeff i j (f - g) x = doubleCoeff i j f x - doubleCoeff i j g x := by
  change Φ 4 2 j (Φ 4 0 i (f - g)) x = _
  rw [show Φ 4 0 i (f - g) = Φ 4 0 i f - Φ 4 0 i g from funext (coeff_sub hf hg 0 i)]
  exact coeff_sub (continuous_blockFourierCoefficient 0 i hf)
    (continuous_blockFourierCoefficient 0 i hg) 2 j x

theorem doubleCoeff_smul (c : ℂ) (f : G₄ → ℂ) (i j : ℤ) (x : G₄) :
    doubleCoeff i j (c • f) x = c * doubleCoeff i j f x := by
  change Φ 4 2 j (Φ 4 0 i (c • f)) x = _
  rw [show Φ 4 0 i (c • f) = c • Φ 4 0 i f from
    funext (blockFourierCoefficient_smul 0 i c f), blockFourierCoefficient_smul]

private theorem doubleCoeff_zero (i j : ℤ) (x : G₄) :
    doubleCoeff i j (0 : G₄ → ℂ) x = 0 := by
  change Φ 4 2 j (Φ 4 0 i (0 : G₄ → ℂ)) x = 0
  rw [show Φ 4 0 i (0 : G₄ → ℂ) = 0 from funext (blockFourierCoefficient_zero_fun 0 i),
    blockFourierCoefficient_zero_fun]

private theorem eq_of_doubleCoeff_eq {ds : List RealBlock} {f g : KF 4 ds}
    (h : ∀ i j : ℤ, ∀ x ∈ K₄, doubleCoeff i j f x = doubleCoeff i j g x) : f = g := by
  apply eq_of_blockFourierCoefficient_eq (p := 0) (by decide)
  intro i x hx
  let a := Φ 4 0 i (f : G₄ → ℂ)
  let b := Φ 4 0 i (g : G₄ → ℂ)
  have ha := continuous_blockFourierCoefficient 0 i (continuous_coe f)
  have hb := continuous_blockFourierCoefficient 0 i (continuous_coe g)
  have haK := RealSwapFLanding.mem_kFiniteVectors_blockFourierCoefficient 0 i (continuous_coe f) f.2.2
  have hbK := RealSwapFLanding.mem_kFiniteVectors_blockFourierCoefficient 0 i (continuous_coe g) g.2.2
  apply sub_eq_zero.mp
  change (a - b) x = 0
  apply eq_zero_of_blockFourierCoefficient_eq_zero (p := 2) (by decide)
    (ha.sub hb) (Submodule.sub_mem _ haK hbK) hx
  intro j
  rw [coeff_sub ha hb, sub_eq_zero]
  exact h i j x hx

/-- The sign separating the positive and negative parts of a high window. -/
def modeSign (i : ℤ) : ℂ := if 0 ≤ i then 1 else -1

/-- The mode factor incurred when changing the chosen parity of a pair. -/
def pairSign (s t : Fin 2) (i : ℤ) : ℂ := if s = t then 1 else modeSign i

private abbrev allowed (d : ComplexCharacterData) (s : Fin 2) (i : ℤ) :=
  Even (i - pairParity (P.lo d s) (P.hi d s))

private theorem pairParity_eq_of_pair (d : ComplexCharacterData) (s t : Fin 2) :
    pairParity (P.lo d s) (P.hi d s) = pairParity (P.lo d t) (P.hi d t) := by
  dsimp [pairParity, P.lo, P.hi, RealJacquetFrobenius.charData]
  omega

private def pairTail (d : ComplexCharacterData) (s : Fin 2) : ℤ → ℂ :=
  tailMultiplier d.weight.natAbs (pairParity (P.lo d s) (P.hi d s))
    ((-1 : ℂ) ^ (P.hi d s).parity.val)

private theorem pairTail_change (d : ComplexCharacterData) (s t : Fin 2) (i : ℤ) :
    pairTail d t i = pairSign s t i * pairTail d s i := by
  by_cases hst : s = t
  · simp only [hst, pairSign, ↓reduceIte, one_mul]
  have hsum : (P.hi d t).parity.val + (P.hi d s).parity.val = 1 := by
    have hv : s.val ≠ t.val := fun h => hst (Fin.ext h)
    have hs := s.isLt
    have ht := t.isLt
    dsimp [P.hi, RealJacquetFrobenius.charData]
    omega
  have hsign : (-1 : ℂ) ^ (P.hi d t).parity.val = -(-1 : ℂ) ^ (P.hi d s).parity.val := by
    by_cases h : (P.hi d s).parity.val = 0
    · rw [h, show (P.hi d t).parity.val = 1 by omega]
      norm_num
    · rw [show (P.hi d s).parity.val = 1 by omega, show (P.hi d t).parity.val = 0 by omega]
      norm_num
  unfold pairTail tailMultiplier pairSign
  rw [pairParity_eq_of_pair d t s, hsign, ite_eq_right hst]
  by_cases hi : 0 ≤ i
  · simp only [extend_of_nonneg hi, modeSign, hi, ↓reduceIte, one_mul]
  · simp only [extend_of_neg (lt_of_not_ge hi), modeSign, hi, ↓reduceIte, neg_mul, one_mul]

private theorem tail_ne_zero_iff (d : ComplexCharacterData) (s : Fin 2)
    (hd : 0 < d.weight.natAbs) {i : ℤ} (hi : allowed d s i) :
    pairTail d s i ≠ 0 ↔ (d.weight.natAbs : ℤ) ≤ |i| := by
  rw [pairTail, tailMultiplier_ne_zero_iff hd (pairParity_eq _ _) (P.pair_parity d s)
    (neg_one_pow_sq_fin _) hi]
  exact ⟨le_of_lt, fun h =>
    lt_of_not_ge (fun hn => not_lt_of_ge h (abs_lt_of_parity (P.pair_parity d s) hi hn))⟩

private theorem double_zero_of_parity {sd se : Fin 2}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) (f : KF 4 (P.X d e sd se))
    {i j : ℤ} (hbad : ¬ allowed d sd i ∨ ¬ allowed e se j) {x : G₄} (hx : x ∈ K₄) :
    doubleCoeff i j f x = 0 := by
  rcases hbad with hi | hj
  · let h := P.dataDd d e sd se hd
    have hzero : ∀ g ∈ K₄, Φ 4 0 i f g = 0 :=
      fun g _ => blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hi g
    exact (blockFourierCoefficient_congr_on_compact hzero hx j).trans
      (blockFourierCoefficient_zero_fun 2 j x)
  · let h := P.dataDeX d e sd se he
    have hzero : ∀ g ∈ K₄, Φ 4 2 j f g = 0 :=
      fun g _ => blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj g
    rw [show doubleCoeff i j f x = Φ 4 2 j (Φ 4 0 i f) x from rfl,
      ← blockFourierCoefficient_comm outer_disjoint (continuous_coe f)]
    exact (blockFourierCoefficient_congr_on_compact hzero hx i).trans
      (blockFourierCoefficient_zero_fun 0 i x)

private theorem quotient_doubleCoeff {sd se : Fin 2}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) (f : KF 4 (P.X d e sd se))
    (i j : ℤ) {x : G₄} (hx : x ∈ K₄) :
    doubleCoeff i j (P.quotientMap d e sd se hd he f) x =
      (pairTail d sd i * pairTail e se j) * doubleCoeff i j f x := by
  let u := P.Dd d e sd se hd f
  let v := P.De d e sd se he u
  change doubleCoeff i j (ofEqMap (P.KF_Z d e sd se) v) x = _
  rw [ofEqMap_apply_coe]
  change Φ 4 2 j (Φ 4 0 i v) x = _
  rw [← blockFourierCoefficient_comm outer_disjoint (continuous_coe v)]
  have hv := coeff_multiplier (q := 0) (fun j y hy =>
    blockFourierCoefficient_blockFrobMap (P.dataDe d e sd se he) u (j := j) hy) j i hx
  have hu := coeff_multiplier (q := 2) (fun i y hy =>
    blockFourierCoefficient_blockFrobMap (P.dataDd d e sd se hd) f (j := i) hy) i j hx
  change Φ 4 0 i (Φ 4 2 j v) x = pairTail e se j * Φ 4 0 i (Φ 4 2 j u) x at hv
  change Φ 4 2 j (Φ 4 0 i u) x = pairTail d sd i * Φ 4 2 j (Φ 4 0 i f) x at hu
  rw [hv, blockFourierCoefficient_comm outer_disjoint (continuous_coe u), hu]
  change _ = (pairTail d sd i * pairTail e se j) * Φ 4 2 j (Φ 4 0 i f) x
  ring

/-- Compare two outer quotient maps by their double coefficients in the
unsigned high windows. Changing the parity of a pair inserts its mode sign. -/
theorem quotient_eq_iff {sd se td te : Fin 2}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (f : KF 4 (P.X d e sd se)) (g : KF 4 (P.X d e td te)) :
    P.quotientMap d e sd se hd he f = P.quotientMap d e td te hd he g ↔
    ∀ i j : ℤ, (d.weight.natAbs : ℤ) ≤ |i| → (e.weight.natAbs : ℤ) ≤ |j| →
      ∀ x ∈ K₄, doubleCoeff i j f x = (pairSign sd td i * pairSign se te j) * doubleCoeff i j g x := by
  have hpar₀ (i : ℤ) : allowed d sd i ↔ allowed d td i := by
    change Even (i - pairParity (P.lo d sd) (P.hi d sd)) ↔
      Even (i - pairParity (P.lo d td) (P.hi d td))
    rw [pairParity_eq_of_pair d td sd]
  have hpar₂ (j : ℤ) : allowed e se j ↔ allowed e te j := by
    change Even (j - pairParity (P.lo e se) (P.hi e se)) ↔
      Even (j - pairParity (P.lo e te) (P.hi e te))
    rw [pairParity_eq_of_pair e te se]
  have hbad (i j : ℤ) (hb : ¬ allowed d sd i ∨ ¬ allowed e se j) (x : G₄) (hx : x ∈ K₄) :
      doubleCoeff i j f x = 0 ∧ doubleCoeff i j g x = 0 :=
    ⟨double_zero_of_parity hd he f hb hx,
      double_zero_of_parity hd he g (hb.imp
        (fun h hn => h ((hpar₀ i).mpr hn)) (fun h hn => h ((hpar₂ j).mpr hn))) hx⟩
  constructor
  · intro h i j hi hj x hx
    by_cases hpi : allowed d sd i
    · by_cases hpj : allowed e se j
      · have hh := congrArg (fun v : KF 4 [.induced d, .induced e] => doubleCoeff i j v x) h
        rw [quotient_doubleCoeff hd he f i j hx, quotient_doubleCoeff hd he g i j hx,
          pairTail_change d sd td, pairTail_change e se te] at hh
        apply mul_left_cancel₀ (mul_ne_zero ((tail_ne_zero_iff d sd hd hpi).mpr hi)
          ((tail_ne_zero_iff e se he hpj).mpr hj))
        linear_combination hh
      · rw [(hbad i j (Or.inr hpj) x hx).1, (hbad i j (Or.inr hpj) x hx).2, mul_zero]
    · rw [(hbad i j (Or.inl hpi) x hx).1, (hbad i j (Or.inl hpi) x hx).2, mul_zero]
  · intro h
    apply eq_of_doubleCoeff_eq
    intro i j x hx
    rw [quotient_doubleCoeff hd he f i j hx, quotient_doubleCoeff hd he g i j hx,
      pairTail_change d sd td, pairTail_change e se te]
    by_cases hpi : allowed d sd i
    · by_cases hpj : allowed e se j
      · by_cases hi : (d.weight.natAbs : ℤ) ≤ |i|
        · by_cases hj : (e.weight.natAbs : ℤ) ≤ |j|
          · rw [h i j hi hj x hx]
            ring
          · have hz : pairTail e se j = 0 := not_ne_iff.mp (mt (tail_ne_zero_iff e se he hpj).mp hj)
            rw [hz]
            ring
        · have hz : pairTail d sd i = 0 := not_ne_iff.mp (mt (tail_ne_zero_iff d sd hd hpi).mp hi)
          rw [hz]
          ring
      · rw [(hbad i j (Or.inr hpj) x hx).1, (hbad i j (Or.inr hpj) x hx).2, mul_zero, mul_zero]
    · rw [(hbad i j (Or.inl hpi) x hx).1, (hbad i j (Or.inl hpi) x hx).2, mul_zero, mul_zero]

private theorem quotient_zero_iff {sd se : Fin 2}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) (f : KF 4 (P.X d e sd se)) :
    P.quotientMap d e sd se hd he f = 0 ↔
    ∀ i j : ℤ, (d.weight.natAbs : ℤ) ≤ |i| → (e.weight.natAbs : ℤ) ≤ |j| →
      ∀ x ∈ K₄, doubleCoeff i j f x = 0 := by
  simpa only [map_zero, ZeroMemClass.coe_zero, doubleCoeff_zero, mul_zero] using
    quotient_eq_iff hd he f (0 : KF 4 (P.X d e sd se))

theorem flipParity_ne_self (s : Fin 2) : flipParity s ≠ s := by
  intro h
  have h' := congrArg Fin.val h
  have hs := s.isLt
  dsimp [flipParity] at h'
  omega

private theorem high_band {L H : ℕ} (hL : 0 < L) {i j : ℤ}
    (hi : (L : ℤ) + H ≤ |i|) (hj : i - H ≤ j) (hj' : j ≤ i + H) :
    (L : ℤ) ≤ |j| ∧ modeSign j = modeSign i := by
  by_cases h : 0 ≤ i
  · rw [abs_of_nonneg h] at hi
    have hj₀ : 0 ≤ j := by omega
    exact ⟨by rw [abs_of_nonneg hj₀]; omega, by simp [modeSign, h, hj₀]⟩
  · rw [abs_of_neg (lt_of_not_ge h)] at hi
    have hj₀ : j < 0 := by omega
    exact ⟨by rw [abs_of_neg hj₀]; omega, by simp [modeSign, h, not_le_of_gt hj₀]⟩

theorem middle_coeff (f : KF 4 (source d e k)) (j : ℤ) {x : G₄} (hx : x ∈ K₄) :
    Φ 4 1 j (middle d e k f) x =
      (tailPolynomial (C.cutoff d e k)).eval (j : ℂ) * Φ 4 1 j f x :=
  blockFourierCoefficient_blockFrobMap (middleData d e k) f hx (j := j)

private theorem singular_middle_coeff (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (C.source d e k)) (j : ℤ) {x : G₄} (hx : x ∈ K₄) :
    Φ 4 1 j (C.middleTail h hH f) x =
      (tailPolynomial (C.cutoff d e k)).eval (j : ℂ) * Φ 4 1 j f x := by
  change Φ 4 1 j (blockFrobMap (C.middleTailData h hH) f) x = _
  rw [blockFourierCoefficient_blockFrobMap (C.middleTailData h hH) f hx, C.middle_sign]
  by_cases hj : Even (j - pairParity (P.hi d (M.leftParity d)) (P.lo e (M.rightParity d e k)))
  · rw [tailPolynomial_eq (C.cutoff_pos hH) (pairParity_eq _ _) (C.middle_parity hH) j hj]
  · rw [blockFourierCoefficient_eq_zero_of_not_even (C.middleTailData h hH).lt
      (C.middleTailData h hH).par f hj x, mul_zero, mul_zero]

/-- The lifted representative in the flipped first-pair presentation. -/
abbrev sectionMap (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (k : ℕ) : KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 (source d e k) :=
  P.quotientSection d e (flipParity (M.leftParity d)) (M.rightParity d e k) hd he

private theorem middle_high_zero (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (v : KF 4 [.induced d, .induced e]) (hv : C.quotient hd he h hH v = 0)
    (i j : ℤ) (hi : (d.weight.natAbs : ℤ) + C.cutoff d e k ≤ |i|)
    (hj : (e.weight.natAbs : ℤ) + C.cutoff d e k ≤ |j|) {x : G₄} (hx : x ∈ K₄) :
    doubleCoeff i j (middle d e k (sectionMap hd he k v)) x = 0 := by
  let s := M.leftParity d
  let t := M.rightParity d e k
  let f := sectionMap hd he k v
  let f' := P.quotientSection d e s t hd he v
  let g := middle d e k f
  let g' := C.middleTail h hH f'
  have hsec : P.quotientMap d e (flipParity s) t hd he f = P.quotientMap d e s t hd he f' :=
    (P.quotient_section d e _ _ hd he v).trans (P.quotient_section d e _ _ hd he v).symm
  have hhigh (i j : ℤ) (hi : (d.weight.natAbs : ℤ) ≤ |i|) (hj : (e.weight.natAbs : ℤ) ≤ |j|)
      (y : G₄) (hy : y ∈ K₄) :
      doubleCoeff i j f y = modeSign i * doubleCoeff i j f' y := by
    have hh := (quotient_eq_iff hd he f f').mp hsec i j hi hj y hy
    change doubleCoeff i j f y =
      (pairSign (flipParity s) s i * pairSign t t j) * doubleCoeff i j f' y at hh
    simpa only [pairSign, flipParity_ne_self, ↓reduceIte, mul_one] using hh
  have hg' : C.crossedQuotient d e k (M.inclusion hd he h hH g') = 0 := by
    change C.crossedQuotient d e k (M.inclusion hd he h hH (C.middleTail h hH f')) = 0
    rw [← C.beforeDescent_apply hd he h hH f']
    exact hv
  have hcut := C.crossed_cutoffs hH
  have hzero := (quotient_zero_iff (C.crossed_lower_pos d e k) (C.crossed_upper_pos d e k)
    (M.inclusion hd he h hH g')).mp hg' i j
    (by simpa only [hcut.1, Nat.cast_add] using hi)
    (by simpa only [hcut.2, Nat.cast_add] using hj) x hx
  rw [C.inclusion_coe hd he h hH g'] at hzero
  let c := modeSign i
  have hr := rectangle ((continuous_coe f).sub ((continuous_coe f').const_smul c))
    ((continuous_coe g).sub ((continuous_coe g').const_smul c))
    (Submodule.sub_mem _ f.2.2 (Submodule.smul_mem _ c f'.2.2))
    (Submodule.sub_mem _ g.2.2 (Submodule.smul_mem _ c g'.2.2))
    (tailPolynomial (C.cutoff d e k)) i j
    (fun a y hy => by
      rw [coeff_sub (continuous_coe g) ((continuous_coe g').const_smul c),
        blockFourierCoefficient_smul, coeff_sub (continuous_coe f) ((continuous_coe f').const_smul c),
        blockFourierCoefficient_smul]
      change Φ 4 1 a (middle d e k f) y - c * Φ 4 1 a (C.middleTail h hH f') y = _
      rw [middle_coeff f a hy, singular_middle_coeff h hH f' a hy]
      ring)
    (fun a b ha ha' hb hb' y hy => by
      simp only [tailPolynomial_natDegree] at ha ha' hb hb'
      obtain ⟨hla, hsa⟩ := high_band hd hi ha ha'
      have hlb := (high_band he hj hb hb').1
      change doubleCoeff a b ((f : G₄ → ℂ) - c • (f' : G₄ → ℂ)) y = 0
      rw [doubleCoeff_sub (continuous_coe f) ((continuous_coe f').const_smul c), doubleCoeff_smul,
        hhigh a b hla hlb y hy, hsa]
      exact sub_self _) x hx
  change doubleCoeff i j ((g : G₄ → ℂ) - c • (g' : G₄ → ℂ)) x = 0 at hr
  rw [doubleCoeff_sub (continuous_coe g) ((continuous_coe g').const_smul c),
    doubleCoeff_smul, hzero, mul_zero, sub_zero] at hr
  exact hr

private def middleEquiv (d e : ComplexCharacterData) (k : ℕ) :
    KF 4 (source d e k) ≃ₗ[ℂ] KF 4 (swapped d e k) :=
  { toLinearMap := middle d e k, invFun := inverse d e k
    left_inv := inverse_middle, right_inv := middle_inverse }

private def crossedEquiv (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (source d e k) ≃ₗ[ℂ] KF 4 (crossed d e k) :=
  (middleEquiv d e k).trans (LinearEquiv.ofEq _ _ (congrArg (KF 4) (swapped_eq_crossed hd he h hH)))

private theorem crossedEquiv_coe (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) (f : KF 4 (source d e k)) :
    (crossedEquiv hd he h hH f : G₄ → ℂ) = (middle d e k f : G₄ → ℂ) := by
  rw [crossedEquiv, LinearEquiv.trans_apply]
  change (ofEqMap (congrArg (KF 4) (swapped_eq_crossed hd he h hH)) (middle d e k f) :
    G₄ → ℂ) = (middle d e k f : G₄ → ℂ)
  exact ofEqMap_apply_coe _ _

/-- In the flipped presentation, a section of a vector in the positive
crossed kernel splits into two summands with single-axis low polynomial images. -/
theorem exists_split (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (v : KF 4 [.induced d, .induced e]) (hv : C.quotient hd he h hH v = 0) :
    ∃ f₀ f₂ : KF 4 (source d e k), sectionMap hd he k v = f₀ + f₂ ∧
      (∀ j : ℤ, (d.weight.natAbs : ℤ) + C.cutoff d e k ≤ |j| →
        ∀ x ∈ K₄, Φ 4 0 j (middle d e k f₀) x = 0) ∧
      (∀ j : ℤ, (e.weight.natAbs : ℤ) + C.cutoff d e k ≤ |j| →
        ∀ x ∈ K₄, Φ 4 2 j (middle d e k f₂) x = 0) := by
  let A := lowerData d e k
  let B := upperData d e k
  let s := flipParity (C.crossedLeftParity d e k)
  let E := crossedEquiv hd he h hH
  let f := sectionMap hd he k v
  let g := E f
  let hA := C.crossed_lower_pos d e k
  let hB := C.crossed_upper_pos d e k
  have hcut := C.crossed_cutoffs hH
  have hg : g ∈ LinearMap.ker (P.quotientMap A B s 0 hA hB) := by
    apply LinearMap.mem_ker.mpr
    apply (quotient_zero_iff hA hB g).mpr
    intro i j hi hj x hx
    change doubleCoeff i j (crossedEquiv hd he h hH f) x = 0
    rw [crossedEquiv_coe]
    exact middle_high_zero hd he h hH v hv i j
      (by simpa only [A, hcut.1, Nat.cast_add] using hi)
      (by simpa only [B, hcut.2, Nat.cast_add] using hj) hx
  rw [P.ker_quotient] at hg
  obtain ⟨g₀, ⟨z₀, rfl⟩, g₂, ⟨z₂, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hg
  let f₀ := E.symm (P.qd A B s 0 z₀)
  let f₂ := E.symm (P.qe A B s 0 z₂)
  refine ⟨f₀, f₂, ?_, ?_, ?_⟩
  · change f = E.symm (P.qd A B s 0 z₀) + E.symm (P.qe A B s 0 z₂)
    rw [← map_add, hsum, E.symm_apply_apply]
  · intro j hj x hx
    rw [← crossedEquiv_coe hd he h hH f₀]
    change Φ 4 0 j (E (E.symm (P.qd A B s 0 z₀))) x = 0
    rw [E.apply_symm_apply]
    exact C.binomial_low hA (pairParity_eq _ _) (P.pair_parity A s)
      (P.dataQd A B s 0) z₀ x hx j (by simpa only [A, hcut.1, Nat.cast_add] using hj)
  · intro j hj x hx
    rw [← crossedEquiv_coe hd he h hH f₂]
    change Φ 4 2 j (E (E.symm (P.qe A B s 0 z₂))) x = 0
    rw [E.apply_symm_apply]
    exact C.binomial_low hB (pairParity_eq _ _) (P.pair_parity B 0)
      (P.dataQe A B s 0) z₂ x hx j (by simpa only [B, hcut.2, Nat.cast_add] using hj)

end Langlands.Archimedean.RealInducedPairPositiveGenericMiddle

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockJacquet
  RealInducedPairLinkedReplacement RealInducedPairPositiveGenericMiddle

/-- The flipped-presentation section of a positive crossed-kernel vector
splits into two summands with single-axis low polynomial images. -/
def RealInducedPairPositiveGenericMiddleStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (v : KF 4 [.induced d, .induced e]),
    C.quotient hd he h hH v = 0 →
    ∃ f₀ f₂ : KF 4 (source d e k), sectionMap hd he k v = f₀ + f₂ ∧
      (∀ j : ℤ, (d.weight.natAbs : ℤ) + C.cutoff d e k ≤ |j| →
        ∀ x ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 0 j (middle d e k f₀) x = 0) ∧
      (∀ j : ℤ, (e.weight.natAbs : ℤ) + C.cutoff d e k ≤ |j| →
        ∀ x ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 2 j (middle d e k f₂) x = 0)

theorem realInducedPairPositiveGenericMiddle : RealInducedPairPositiveGenericMiddleStatement :=
  fun _ _ _ hd he h hH v => exists_split hd he h hH v

end Langlands.Archimedean
