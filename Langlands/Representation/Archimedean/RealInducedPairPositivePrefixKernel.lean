import Langlands.Representation.Archimedean.RealAdjacentFourierBand
import Langlands.Representation.Archimedean.RealInducedPairPositiveTwoPrefix

/-! # The two positive prefixes lie in the crossed quotient kernel -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairPositivePrefixKernel

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockJacquet
  RealBlockFourierFinite RealBlockFrobeniusMap RealBlockFrobeniusDisjoint
  RealBlockMultiplier RealCharacterPair RealCharacterPairReducible
  RealInducedPairAscendingExchange RealInducedPairLinkedReplacement
  RealInducedPairCrossedReplacement RealTailMultiplierPolynomial RealAdjacentFourierBand

namespace A
export RealInducedPairQuotientPresentation (T KF_Z quotient_section pair_parity)
end A

namespace C
export RealInducedPairPositiveCrossedQuotient (source cutoff cutoff_pos middle_parity
  middle_sign middleTailData middleTail crossedLeftParity crossedSource crossedQuotient
  crossed_lower_pos crossed_upper_pos crossed_cutoffs beforeDescent_apply inclusion_coe quotient)
end C

namespace K
export RealInducedPairPositiveCrossedKernel (prefix_le_ker)
end K

namespace M
export RealInducedPairCrossedMiddleQuotient (leftParity rightParity inclusion)
end M

namespace D
export RealInducedPairDistantParity (innerBinomial)
end D

namespace O
export RealInducedPairPositiveOppositeOuter (flipParity)
end O

namespace F
export RealInducedPairPositiveTwoPrefix (oppositePrefix totalPrefix Absorption absorption_iff_ker_le)
end F

local notation "Φ" => blockFourierCoefficient
local notation "G₄" => Langlands.GeneralLinear 4 ℝ
local notation "K₄" => unitaryCompact ℝ 4

private def doubleCoeff (i j : ℤ) (f : G₄ → ℂ) : G₄ → ℂ :=
  Φ 4 2 j (Φ 4 0 i f)

private theorem outer_disjoint : (0 + 1 < (2 : ℕ)) ∨ 2 + 1 < 0 := Or.inl (by decide)

private theorem doubleCoeff_zero_left {f : G₄ → ℂ} {i j : ℤ} {g : G₄} (hg : g ∈ K₄)
    (h : ∀ x ∈ K₄, Φ 4 0 i f x = 0) : doubleCoeff i j f g = 0 :=
  (blockFourierCoefficient_congr_on_compact h hg j).trans
    (blockFourierCoefficient_zero_fun 2 j g)

private theorem doubleCoeff_zero_right {f : G₄ → ℂ} (hf : Continuous f) {i j : ℤ}
    {g : G₄} (hg : g ∈ K₄) (h : ∀ x ∈ K₄, Φ 4 2 j f x = 0) :
    doubleCoeff i j f g = 0 := by
  rw [doubleCoeff, ← blockFourierCoefficient_comm outer_disjoint hf]
  exact (blockFourierCoefficient_congr_on_compact h hg i).trans
    (blockFourierCoefficient_zero_fun 0 i g)

private theorem doubleCoeff_sub {f g : G₄ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (i j : ℤ) (x : G₄) :
    doubleCoeff i j (f - g) x = doubleCoeff i j f x - doubleCoeff i j g x := by
  unfold doubleCoeff
  rw [show Φ 4 0 i (f - g) = Φ 4 0 i f - Φ 4 0 i g from funext (coeff_sub hf hg 0 i)]
  exact coeff_sub (continuous_blockFourierCoefficient 0 i hf)
    (continuous_blockFourierCoefficient 0 i hg) 2 j x

private theorem doubleCoeff_smul (c : ℂ) (f : G₄ → ℂ) (i j : ℤ) (x : G₄) :
    doubleCoeff i j (c • f) x = c * doubleCoeff i j f x := by
  unfold doubleCoeff
  rw [show Φ 4 0 i (c • f) = c • Φ 4 0 i f from
    funext (blockFourierCoefficient_smul 0 i c f), blockFourierCoefficient_smul]

private def pairTail (d : ComplexCharacterData) (s : Fin 2) : ℤ → ℂ :=
  tailMultiplier d.weight.natAbs (pairParity (P.lo d s) (P.hi d s))
    ((-1 : ℂ) ^ (P.hi d s).parity.val)

private theorem quotientMap_doubleCoeff {d e : ComplexCharacterData} {sd se : Fin 2}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) (f : KF 4 (P.X d e sd se))
    (i j : ℤ) {x : G₄} (hx : x ∈ K₄) :
    doubleCoeff i j (P.quotientMap d e sd se hd he f) x =
      (pairTail d sd i * pairTail e se j) * doubleCoeff i j f x := by
  let u := P.Dd d e sd se hd f
  let v := P.De d e sd se he u
  change doubleCoeff i j (ofEqMap (A.KF_Z d e sd se) v) x = _
  rw [ofEqMap_apply_coe, doubleCoeff, ← blockFourierCoefficient_comm outer_disjoint (continuous_coe v)]
  have hv := coeff_multiplier (q := 0) (fun j y hy =>
    blockFourierCoefficient_blockFrobMap (P.dataDe d e sd se he) u (j := j) hy) j i hx
  have hu := coeff_multiplier (q := 2) (fun i y hy =>
    blockFourierCoefficient_blockFrobMap (P.dataDd d e sd se hd) f (j := i) hy) i j hx
  change Φ 4 0 i (Φ 4 2 j v) x = _
  change Φ 4 0 i (Φ 4 2 j v) x = pairTail e se j * Φ 4 0 i (Φ 4 2 j u) x at hv
  change Φ 4 2 j (Φ 4 0 i u) x = pairTail d sd i * Φ 4 2 j (Φ 4 0 i f) x at hu
  rw [hv, blockFourierCoefficient_comm outer_disjoint (continuous_coe u), hu]
  unfold doubleCoeff
  ring

private theorem pairParity_flip (d : ComplexCharacterData) (s : Fin 2) :
    pairParity (P.lo d (O.flipParity s)) (P.hi d (O.flipParity s)) =
      pairParity (P.lo d s) (P.hi d s) := by
  dsimp [pairParity, P.lo, P.hi, RealJacquetFrobenius.charData, O.flipParity]
  omega

private theorem middleParity_flip (d e : ComplexCharacterData) (s t : Fin 2) :
    pairParity (P.hi d (O.flipParity s)) (P.lo e (O.flipParity t)) =
      pairParity (P.hi d s) (P.lo e t) := by
  dsimp [pairParity, P.lo, P.hi, RealJacquetFrobenius.charData, O.flipParity]
  omega

private theorem hi_sign_flip (d : ComplexCharacterData) (s : Fin 2) :
    (-1 : ℂ) ^ (P.hi d (O.flipParity s)).parity.val = -(-1 : ℂ) ^ (P.hi d s).parity.val := by
  have hsum : (P.hi d (O.flipParity s)).parity.val + (P.hi d s).parity.val = 1 := by
    dsimp [P.hi, RealJacquetFrobenius.charData, O.flipParity]
    omega
  by_cases h : (P.hi d s).parity.val = 0
  · rw [h, show (P.hi d (O.flipParity s)).parity.val = 1 by omega]
    norm_num
  · rw [show (P.hi d s).parity.val = 1 by have := (P.hi d s).parity.isLt; omega,
      show (P.hi d (O.flipParity s)).parity.val = 0 by omega]
    norm_num

private def modeSign (i : ℤ) : ℂ := if 0 ≤ i then 1 else -1

private theorem pairTail_flip (d : ComplexCharacterData) (s : Fin 2) (i : ℤ) :
    pairTail d (O.flipParity s) i = modeSign i * pairTail d s i := by
  unfold pairTail tailMultiplier
  rw [pairParity_flip, hi_sign_flip]
  by_cases h : 0 ≤ i
  · simp only [extend_of_nonneg h, modeSign, h, ↓reduceIte, one_mul]
  · simp only [extend_of_neg (lt_of_not_ge h), modeSign, h, ↓reduceIte,
      neg_mul, one_mul]

private theorem pairTail_ne_zero {d : ComplexCharacterData} {s : Fin 2} {i : ℤ}
    (hd : 0 < d.weight.natAbs) (hi : Even (i - pairParity (P.lo d s) (P.hi d s)))
    (hhi : (d.weight.natAbs : ℤ) ≤ |i|) : pairTail d s i ≠ 0 := by
  apply (tailMultiplier_ne_zero_iff hd (pairParity_eq _ _) (A.pair_parity d s)
    (neg_one_pow_sq_fin _) hi).mpr
  by_contra hn
  exact (not_lt_of_ge hhi) (abs_lt_of_parity (A.pair_parity d s) hi (le_of_not_gt hn))

private theorem quotientSection_high {d e : ComplexCharacterData} {sd se : Fin 2}
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (f : KF 4 (P.X d e (O.flipParity sd) (O.flipParity se))) (i j : ℤ)
    (hi : (d.weight.natAbs : ℤ) ≤ |i|) (hj : (e.weight.natAbs : ℤ) ≤ |j|)
    {x : G₄} (hx : x ∈ K₄) :
    doubleCoeff i j (P.quotientSection d e sd se hd he
      (P.quotientMap d e (O.flipParity sd) (O.flipParity se) hd he f)) x =
      (modeSign i * modeSign j) * doubleCoeff i j f x := by
  let v := P.quotientMap d e (O.flipParity sd) (O.flipParity se) hd he f
  let s := P.quotientSection d e sd se hd he v
  change doubleCoeff i j s x = _
  by_cases hpi : Even (i - pairParity (P.lo d sd) (P.hi d sd))
  · by_cases hpj : Even (j - pairParity (P.lo e se) (P.hi e se))
    · have hv : P.quotientMap d e sd se hd he s = v := A.quotient_section d e sd se hd he v
      have hc := congrArg (fun u : KF 4 [.induced d, .induced e] => doubleCoeff i j u x) hv
      change doubleCoeff i j (P.quotientMap d e sd se hd he s) x =
        doubleCoeff i j (P.quotientMap d e (O.flipParity sd) (O.flipParity se) hd he f) x at hc
      rw [quotientMap_doubleCoeff hd he s i j hx, quotientMap_doubleCoeff hd he f i j hx,
        pairTail_flip, pairTail_flip] at hc
      apply mul_left_cancel₀ (mul_ne_zero (pairTail_ne_zero hd hpi hi) (pairTail_ne_zero he hpj hj))
      linear_combination hc
    · have h₀ := P.dataDeX d e sd se he
      have h₁ := P.dataDeX d e (O.flipParity sd) (O.flipParity se) he
      have hpj' : ¬ Even (j - pairParity (P.lo e (O.flipParity se)) (P.hi e (O.flipParity se))) := by
        rwa [pairParity_flip]
      rw [doubleCoeff_zero_right (continuous_coe s) hx
          (fun g _ => blockFourierCoefficient_eq_zero_of_not_even h₀.lt h₀.par s hpj g),
        doubleCoeff_zero_right (continuous_coe f) hx
          (fun g _ => blockFourierCoefficient_eq_zero_of_not_even h₁.lt h₁.par f hpj' g), mul_zero]
  · have h₀ := P.dataDd d e sd se hd
    have h₁ := P.dataDd d e (O.flipParity sd) (O.flipParity se) hd
    have hpi' : ¬ Even (i - pairParity (P.lo d (O.flipParity sd)) (P.hi d (O.flipParity sd))) := by
      rwa [pairParity_flip]
    rw [doubleCoeff_zero_left hx
        (fun g _ => blockFourierCoefficient_eq_zero_of_not_even h₀.lt h₀.par s hpi g),
      doubleCoeff_zero_left hx
        (fun g _ => blockFourierCoefficient_eq_zero_of_not_even h₁.lt h₁.par f hpi' g), mul_zero]

private theorem high_band {L H : ℕ} (hL : 0 < L) {i a : ℤ}
    (hi : (L : ℤ) + H ≤ |i|) (ha : i - H ≤ a) (ha' : a ≤ i + H) :
    (L : ℤ) ≤ |a| ∧ modeSign a = modeSign i := by
  by_cases hi₀ : 0 ≤ i
  · rw [abs_of_nonneg hi₀] at hi
    have ha₀ : 0 ≤ a := by omega
    exact ⟨by rw [abs_of_nonneg ha₀]; omega, by simp [modeSign, ha₀, hi₀]⟩
  · have hi' : i < 0 := lt_of_not_ge hi₀
    rw [abs_of_neg hi'] at hi
    have ha₀ : ¬ 0 ≤ a := by omega
    exact ⟨by rw [abs_of_neg (lt_of_not_ge ha₀)]; omega, by simp [modeSign, ha₀, hi₀]⟩

variable {d e : ComplexCharacterData} {k : ℕ}

local notation "sd" => M.leftParity d
local notation "se" => M.rightParity d e k
local notation "sd'" => O.flipParity (M.leftParity d)
local notation "se'" => O.flipParity (M.rightParity d e k)
local notation "H" => C.cutoff d e k

private theorem middleTail_polynomial (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (C.source d e k)) (j : ℤ) {g : G₄} (hg : g ∈ K₄) :
    Φ 4 1 j (C.middleTail h hH f) g =
      (tailPolynomial H).eval (j : ℂ) * Φ 4 1 j f g := by
  change Φ 4 1 j (blockFrobMap (C.middleTailData h hH) f) g = _
  rw [blockFourierCoefficient_blockFrobMap (C.middleTailData h hH) f hg, C.middle_sign]
  by_cases hj : Even (j - pairParity (P.hi d sd) (P.lo e se))
  · rw [tailPolynomial_eq (C.cutoff_pos hH) (pairParity_eq _ _) (C.middle_parity hH) j hj]
  · rw [blockFourierCoefficient_eq_zero_of_not_even (C.middleTailData h hH).lt
      (C.middleTailData h hH).par f hj g, mul_zero, mul_zero]

private theorem oppositeBinomial_polynomial_zero (hH : 0 < innerWeight d e k)
    (z : KF 4 (X1 d e sd' se')) (j : ℤ) {g : G₄} (hg : g ∈ K₄) :
    (tailPolynomial H).eval (j : ℂ) * Φ 4 1 j (D.innerBinomial d e k sd' se' z) g = 0 := by
  let ε := pairParity (P.hi d sd') (P.lo e se')
  have hpar : Even ((H : ℤ) - 1 - ε) := by
    dsimp only [ε]
    rw [middleParity_flip]
    exact C.middle_parity hH
  let hq : IsBlockFrobData 4 (X1 d e sd' se') (P.X d e sd' se') 1 ε
      (sigma0 (P.hi d sd') (P.lo e se')) (binomialMultiplier H ε) :=
    data_q0 (n := 4) (pre := [.character (P.lo d sd')])
      (post := [.character (P.hi e se')]) (c := P.hi d sd') (d := P.lo e se') (ℓ := H) rfl
  change (tailPolynomial H).eval (j : ℂ) * Φ 4 1 j (blockFrobMap hq z) g = 0
  by_cases hlow : (H : ℤ) ≤ |j|
  · have hb := RealInducedPairPositiveCrossedQuotient.binomial_low
      (C.cutoff_pos hH) (pairParity_eq _ _) hpar hq z g hg j hlow
    rw [hb, mul_zero]
  · rw [blockFourierCoefficient_blockFrobMap hq z hg]
    by_cases hj : Even (j - ε)
    · rw [← tailPolynomial_eq (C.cutoff_pos hH) (pairParity_eq _ _) hpar j hj]
      have hz : tailMultiplier H ε ((-1 : ℂ) ^ H) j = 0 := by
        by_contra hn
        exact hlow ((tailMultiplier_ne_zero_iff (C.cutoff_pos hH) (pairParity_eq _ _)
          hpar (neg_one_pow_sq H) hj).mp hn).le
      rw [hz, zero_mul]
    · rw [blockFourierCoefficient_eq_zero_of_not_even hq.lt hq.par z hj g,
        mul_zero, mul_zero]

private theorem section_middleTail_high (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (z : KF 4 (X1 d e sd' se')) (i j : ℤ)
    (hi : (d.weight.natAbs : ℤ) + H ≤ |i|) (hj : (e.weight.natAbs : ℤ) + H ≤ |j|)
    {g : G₄} (hg : g ∈ K₄) :
    doubleCoeff i j (C.middleTail h hH
      (P.quotientSection d e sd se hd he (F.oppositePrefix (k := k) hd he z))) g = 0 := by
  let f := D.innerBinomial d e k sd' se' z
  let s := P.quotientSection d e sd se hd he (F.oppositePrefix (k := k) hd he z)
  let c := modeSign i * modeSign j
  apply rectangle ((continuous_coe s).sub ((continuous_coe f).const_smul c))
    (continuous_coe (C.middleTail h hH s))
    (Submodule.sub_mem _ s.2.2 (Submodule.smul_mem _ c f.2.2)) (C.middleTail h hH s).2.2
    (tailPolynomial H) i j _ _ g hg
  · intro a x hx
    rw [coeff_sub (continuous_coe s) ((continuous_coe f).const_smul c),
      blockFourierCoefficient_smul, middleTail_polynomial h hH s a hx,
      mul_sub, mul_left_comm _ c, oppositeBinomial_polynomial_zero hH z a hx,
      mul_zero, sub_zero]
  · intro a b ha ha' hb hb' x hx
    simp only [tailPolynomial_natDegree] at ha ha' hb hb'
    obtain ⟨hha, hsa⟩ := high_band hd hi ha ha'
    obtain ⟨hhb, hsb⟩ := high_band he hj hb hb'
    change doubleCoeff a b ((s : G₄ → ℂ) - c • (f : G₄ → ℂ)) x = 0
    rw [doubleCoeff_sub (continuous_coe s) ((continuous_coe f).const_smul c),
      doubleCoeff_smul]
    have hs := quotientSection_high hd he f a b hha hhb hx
    change doubleCoeff a b s x = _ at hs
    rw [hs, hsa, hsb]
    exact sub_self _

private theorem crossedQuotient_eq_zero {f : KF 4 (C.crossedSource d e k)}
    (hhigh : ∀ i j : ℤ,
      ((lowerData d e k).weight.natAbs : ℤ) ≤ |i| →
      ((upperData d e k).weight.natAbs : ℤ) ≤ |j| →
      ∀ g ∈ K₄, doubleCoeff i j f g = 0) :
    C.crossedQuotient d e k f = 0 := by
  let v := C.crossedQuotient d e k f
  apply eq_of_blockFourierCoefficient_eq (p := 0) (by decide)
  intro i g hg
  change Φ 4 0 i v g = Φ 4 0 i (↑(0 : KF 4 (crossedPair d e k))) g
  simp only [ZeroMemClass.coe_zero, blockFourierCoefficient_zero]
  apply eq_zero_of_blockFourierCoefficient_eq_zero (p := 2) (by decide)
    (continuous_blockFourierCoefficient 0 i (continuous_coe v))
    (RealSwapFLanding.mem_kFiniteVectors_blockFourierCoefficient 0 i (continuous_coe v) v.2.2) hg
  intro j
  change doubleCoeff i j v g = 0
  change doubleCoeff i j (P.quotientMap (lowerData d e k) (upperData d e k)
    (C.crossedLeftParity d e k) 0 (C.crossed_lower_pos d e k) (C.crossed_upper_pos d e k) f) g = 0
  rw [quotientMap_doubleCoeff _ _ f i j hg]
  by_cases hi : ((lowerData d e k).weight.natAbs : ℤ) ≤ |i|
  · by_cases hj : ((upperData d e k).weight.natAbs : ℤ) ≤ |j|
    · rw [hhigh i j hi hj g hg, mul_zero]
    · by_cases hpj : Even (j - pairParity (P.lo (upperData d e k) 0) (P.hi (upperData d e k) 0))
      · have hz : pairTail (upperData d e k) 0 j = 0 := by
          by_contra hn
          exact hj ((tailMultiplier_ne_zero_iff (C.crossed_upper_pos d e k) (pairParity_eq _ _)
            (A.pair_parity _ _) (neg_one_pow_sq_fin _) hpj).mp hn).le
        rw [hz, mul_zero, zero_mul]
      · have hDe := P.dataDeX (lowerData d e k) (upperData d e k)
          (C.crossedLeftParity d e k) 0 (C.crossed_upper_pos d e k)
        rw [doubleCoeff_zero_right (continuous_coe f) hg
          (fun x _ => blockFourierCoefficient_eq_zero_of_not_even hDe.lt hDe.par f hpj x),
          mul_zero]
  · by_cases hpi : Even (i - pairParity (P.lo (lowerData d e k) (C.crossedLeftParity d e k))
      (P.hi (lowerData d e k) (C.crossedLeftParity d e k)))
    · have hz : pairTail (lowerData d e k) (C.crossedLeftParity d e k) i = 0 := by
        by_contra hn
        exact hi ((tailMultiplier_ne_zero_iff (C.crossed_lower_pos d e k) (pairParity_eq _ _)
          (A.pair_parity _ _) (neg_one_pow_sq_fin _) hpi).mp hn).le
      rw [hz, zero_mul, zero_mul]
    · have hDd := P.dataDd (lowerData d e k) (upperData d e k)
        (C.crossedLeftParity d e k) 0 (C.crossed_lower_pos d e k)
      rw [doubleCoeff_zero_left hg
        (fun x _ => blockFourierCoefficient_eq_zero_of_not_even hDd.lt hDd.par f hpi x),
        mul_zero]

theorem oppositePrefix_le_ker (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.range (F.oppositePrefix (k := k) hd he) ≤ LinearMap.ker (C.quotient hd he h hH) := by
  rintro _ ⟨z, rfl⟩
  apply LinearMap.mem_ker.mpr
  let s := P.quotientSection d e sd se hd he (F.oppositePrefix (k := k) hd he z)
  change RealInducedPairPositiveCrossedQuotient.beforeDescent hd he h hH s = 0
  rw [C.beforeDescent_apply]
  apply crossedQuotient_eq_zero
  intro i j hi hj g hg
  rw [C.inclusion_coe]
  obtain ⟨hL, hM⟩ := C.crossed_cutoffs hH
  rw [hL, Nat.cast_add] at hi
  rw [hM, Nat.cast_add] at hj
  exact section_middleTail_high hd he h hH z i j hi hj hg

theorem totalPrefix_le_ker (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    F.totalPrefix (k := k) hd he ≤ LinearMap.ker (C.quotient hd he h hH) :=
  sup_le (K.prefix_le_ker hd he h hH) (oppositePrefix_le_ker hd he h hH)

theorem absorption_iff_ker_eq (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    F.Absorption hd he h hH ↔
      LinearMap.ker (C.quotient hd he h hH) = F.totalPrefix (k := k) hd he := by
  rw [F.absorption_iff_ker_le hd he h hH]
  exact ⟨fun hh => le_antisymm hh (totalPrefix_le_ker hd he h hH), le_of_eq⟩

end Langlands.Archimedean.RealInducedPairPositivePrefixKernel

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement

/-- For a linked positive-inner pair, both outer parity prefixes lie in the
kernel of the actual crossed quotient. -/
def RealInducedPairPositivePrefixKernelStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k),
    RealInducedPairPositiveTwoPrefix.totalPrefix (k := k) hd he ≤
      LinearMap.ker (RealInducedPairPositiveCrossedQuotient.quotient hd he h hH)

theorem realInducedPairPositivePrefixKernel : RealInducedPairPositivePrefixKernelStatement :=
  fun _ _ _ hd he h hH => RealInducedPairPositivePrefixKernel.totalPrefix_le_ker hd he h hH

end Langlands.Archimedean
