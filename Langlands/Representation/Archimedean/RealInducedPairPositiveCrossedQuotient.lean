import Langlands.Representation.Archimedean.RealInducedPairCrossedMiddleQuotient
import Langlands.Representation.Archimedean.RealAmbientPolynomialFourierPropagation

/-! # An actual positive-inner quotient onto the crossed induction pair -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairPositiveCrossedQuotient

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier RealBlockJacquet
open RealCharacterPair RealCharacterPairReducible RealInducedPairAscendingExchange
open RealInducedPairLinkedReplacement RealInducedPairCrossedReplacement

namespace M
export RealInducedPairCrossedMiddleQuotient (leftParity rightParity middleList
  outer_parity quotient quotient_exact quotient_surjective inclusion quotient_factorization)
end M

namespace Q
export RealInducedPairQuotientPresentation (X Xd Xe qd qe dataQd dataQe pair_parity
  Dd DeX dataDd dataDeX ker_Dd ker_quotient quotientMap quotientSection descend)
end Q

abbrev u (d : ComplexCharacterData) := P.lo d (M.leftParity d)
abbrev v (d : ComplexCharacterData) := P.hi d (M.leftParity d)
abbrev x (d e : ComplexCharacterData) (k : ℕ) := P.lo e (M.rightParity d e k)
abbrev y (d e : ComplexCharacterData) (k : ℕ) := P.hi e (M.rightParity d e k)
abbrev source (d e : ComplexCharacterData) (k : ℕ) :=
  Q.X d e (M.leftParity d) (M.rightParity d e k)
abbrev cutoff (d e : ComplexCharacterData) (k : ℕ) := (innerWeight d e k).toNat

variable {d e : ComplexCharacterData} {k : ℕ}

theorem cutoff_pos (hH : 0 < innerWeight d e k) : 0 < cutoff d e k := by
  dsimp [cutoff]
  omega

theorem middle_parity (hH : 0 < innerWeight d e k) :
    Even ((cutoff d e k : ℤ) - 1 - pairParity (v d) (x d e k)) :=
  RealInducedPairDistantParity.inner_parity (M.outer_parity hH) hH

theorem middle_sign :
    (-1 : ℂ) ^ (x d e k).parity.val = (-1 : ℂ) ^ cutoff d e k := by
  change (-1 : ℂ) ^ (cutoff d e k % 2) = (-1 : ℂ) ^ cutoff d e k
  exact (neg_one_pow_eq_pow_mod_two (n := cutoff d e k)).symm

theorem middleTailData (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsBlockFrobData 4 (source d e k) (M.middleList d e k) 1
      (pairParity (v d) (x d e k)) ((-1 : ℂ) ^ (x d e k).parity.val)
      (tailMultiplier (cutoff d e k) (pairParity (v d) (x d e k))
        ((-1 : ℂ) ^ (x d e k).parity.val)) :=
  data_D (n := 4) (pre := [.character (u d)]) (post := [.character (y d e k)])
    (c := v d) (d := x d e k) rfl (cutoff_pos hH) (middle_parity hH)
    (RealInducedPairDistantParity.inner_difference h hH)

def middleTail (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (source d e k) →ₗ[ℂ] KF 4 (M.middleList d e k) :=
  blockFrobMap (middleTailData h hH)

theorem middleTail_exact (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (source d e k) (M.middleList d e k) ⊥
      (middleTail h hH) :=
  RealInducedPairQuotientPresentation.tail_exact (n := 4)
    (pre := [.character (u d)]) (post := [.character (y d e k)])
    rfl (cutoff_pos hH) (middle_parity hH)
    (RealInducedPairDistantParity.inner_difference h hH)

theorem middleTail_section (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (M.middleList d e k)) :
    middleTail h hH (RealInducedPairDistantParity.innerSection h (M.outer_parity hH) hH f) = f := by
  have hind : realInducedBlockAt (M.middleList d e k) 1 =
      some (pairInduced (v d) (x d e k) (cutoff d e k)) := rfl
  exact RealCharacterInducedPushforward.tail_inv (cutoff_pos hH) (pairParity_eq _ _)
    (middle_parity hH) (neg_one_pow_sq_fin (x d e k).parity)
    (middleTailData h hH)
    (data_q1 (n := 4) (pre := [.character (u d)]) (post := [.character (y d e k)])
      rfl (cutoff_pos hH) (middle_parity hH)
      (RealInducedPairDistantParity.inner_difference h hH))
    hind (by rw [pairInduced_weight, abs_of_nonneg (Int.natCast_nonneg _)]) f

theorem middleTail_surjective (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    Function.Surjective (middleTail h hH) :=
  fun f => ⟨RealInducedPairDistantParity.innerSection h (M.outer_parity hH) hH f,
    middleTail_section h hH f⟩

section Fourier

variable {n p ℓ : ℕ} {ds es : List RealBlock} {ε : ℤ}

theorem binomial_low (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {τ : ℂ}
    (hq : IsBlockFrobData n ds es p ε τ (binomialMultiplier ℓ ε))
    (f : KF n ds) :
    ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| →
      blockFourierCoefficient n p j (blockFrobMap hq f) g = 0 := by
  intro g hg j hj
  rw [blockFourierCoefficient_blockFrobMap hq f hg]
  by_cases he : Even (j - ε)
  · have hzero : binomialMultiplier ℓ ε j = 0 := by
      by_contra hn
      have hh := (binomialMultiplier_ne_zero_iff hℓ hε hpar he).mp hn
      omega
    rw [hzero, zero_mul]
  · rw [blockFourierCoefficient_eq_zero_of_not_even hq.lt hq.par f he g, mul_zero]

theorem tail_zero_of_low (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {τ : ℂ} (hτ : τ ^ 2 = 1)
    (hD : IsBlockFrobData n ds es p ε τ (tailMultiplier ℓ ε τ))
    (f : KF n ds)
    (hlow : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| →
      blockFourierCoefficient n p j f g = 0) :
    blockFrobMap hD f = 0 := by
  apply eq_of_blockFourierCoefficient_eq hD.lt
  intro j g hg
  rw [blockFourierCoefficient_blockFrobMap hD f hg]
  simp only [ZeroMemClass.coe_zero, blockFourierCoefficient_zero]
  by_cases he : Even (j - ε)
  · by_cases hzero : tailMultiplier ℓ ε τ j = 0
    · rw [hzero, zero_mul]
    · have hj := (tailMultiplier_ne_zero_iff hℓ hε hpar hτ he).mp hzero
      rw [hlow g hg j hj.le, mul_zero]
  · rw [blockFourierCoefficient_eq_zero_of_not_even hD.lt hD.par f he g, mul_zero]

end Fourier

theorem middleTail_low {a r s : ℕ} (ha : a + 3 ≤ 4)
    (hrs : s = 0 ∧ r = 1 ∨ s = 1 ∧ r = 0) (hr : a + r = 1)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (source d e k)) (c : ℕ)
    (hlow : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (c : ℤ) ≤ |j| →
      blockFourierCoefficient 4 (a + s) j f g = 0) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, ((c + cutoff d e k : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient 4 (a + s) j (middleTail h hH f) g = 0 := by
  have hμ : ∀ j : ℤ, ∀ g ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 (a + r) j (middleTail h hH f) g =
        (RealTailMultiplierPolynomial.tailPolynomial (cutoff d e k)).eval (j : ℂ) *
          blockFourierCoefficient 4 (a + r) j f g := by
    intro j g hg
    rw [hr]
    change blockFourierCoefficient 4 1 j (blockFrobMap (middleTailData h hH) f) g = _
    rw [blockFourierCoefficient_blockFrobMap (middleTailData h hH) f hg, middle_sign]
    by_cases he : Even (j - pairParity (v d) (x d e k))
    · rw [RealTailMultiplierPolynomial.tailPolynomial_eq (cutoff_pos hH)
        (pairParity_eq _ _) (middle_parity hH) j he]
    · rw [blockFourierCoefficient_eq_zero_of_not_even (middleTailData h hH).lt
        (middleTailData h hH).par f he g, mul_zero, mul_zero]
  simpa only [RealTailMultiplierPolynomial.tailPolynomial_natDegree] using
    RealAmbientPolynomialFourierPropagation.propagation a ha hrs
      (continuous_coe f) (continuous_coe (middleTail h hH f))
      f.2.2 (middleTail h hH f).2.2
      (RealTailMultiplierPolynomial.tailPolynomial (cutoff d e k)) hμ c hlow

abbrev crossedLeftParity (d e : ComplexCharacterData) (k : ℕ) :=
  RealInducedPairNegativeInnerQuotient.leftParity
    (lowerData d e k) (upperData d e k) (crossedIndex d e)

abbrev crossedSource (d e : ComplexCharacterData) (k : ℕ) :=
  Q.X (lowerData d e k) (upperData d e k) (crossedLeftParity d e k) 0

theorem crossed_lower_pos (d e : ComplexCharacterData) (k : ℕ) :
    0 < (lowerData d e k).weight.natAbs := by
  simpa using (RealInducedPairMiddleParity.weights_pos d e k).1

theorem crossed_upper_pos (d e : ComplexCharacterData) (k : ℕ) :
    0 < (upperData d e k).weight.natAbs := by
  simpa using (RealInducedPairMiddleParity.weights_pos d e k).2

def crossedQuotient (d e : ComplexCharacterData) (k : ℕ) :
    KF 4 (crossedSource d e k) →ₗ[ℂ] KF 4 (crossedPair d e k) :=
  Q.quotientMap (lowerData d e k) (upperData d e k) (crossedLeftParity d e k) 0
    (crossed_lower_pos d e k) (crossed_upper_pos d e k)

theorem mixed_factorization (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    M.quotient hd he h hH =
      (crossedQuotient d e k).comp (M.inclusion hd he h hH) :=
  M.quotient_factorization hd he h hH

theorem crossed_zero_left (f : KF 4 (crossedSource d e k))
    (hlow : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
      ((lowerData d e k).weight.natAbs : ℤ) ≤ |j| →
      blockFourierCoefficient 4 0 j f g = 0) :
    crossedQuotient d e k f = 0 := by
  have hD : Q.Dd (lowerData d e k) (upperData d e k) (crossedLeftParity d e k) 0
      (crossed_lower_pos d e k) f = 0 :=
    tail_zero_of_low (crossed_lower_pos d e k) (pairParity_eq _ _)
      (Q.pair_parity _ _) (neg_one_pow_sq_fin _)
      (Q.dataDd _ _ _ _ (crossed_lower_pos d e k)) f hlow
  apply LinearMap.mem_ker.mp
  change f ∈ LinearMap.ker (Q.quotientMap _ _ _ _
    (crossed_lower_pos d e k) (crossed_upper_pos d e k))
  rw [Q.ker_quotient]
  apply Submodule.mem_sup_left
  rw [← Q.ker_Dd _ _ _ _ (crossed_lower_pos d e k)]
  exact hD

theorem crossed_zero_right (f : KF 4 (crossedSource d e k))
    (hlow : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
      ((upperData d e k).weight.natAbs : ℤ) ≤ |j| →
      blockFourierCoefficient 4 2 j f g = 0) :
    crossedQuotient d e k f = 0 := by
  have hD : Q.DeX (lowerData d e k) (upperData d e k) (crossedLeftParity d e k) 0
      (crossed_upper_pos d e k) f = 0 :=
    tail_zero_of_low (crossed_upper_pos d e k) (pairParity_eq _ _)
      (Q.pair_parity _ _) (neg_one_pow_sq_fin _)
      (Q.dataDeX _ _ _ _ (crossed_upper_pos d e k)) f hlow
  have hker :
      LinearMap.ker (Q.DeX (lowerData d e k) (upperData d e k)
        (crossedLeftParity d e k) 0 (crossed_upper_pos d e k)) =
      LinearMap.range (Q.qe (lowerData d e k) (upperData d e k)
        (crossedLeftParity d e k) 0) :=
    RealInducedPairQuotientPresentation.ker_tail_eq_range (crossed_upper_pos d e k)
      (pairParity_eq _ _) (Q.pair_parity _ _) (neg_one_pow_sq_fin _)
      (Q.dataQe _ _ _ _)
      (data_B (n := 4)
        (pre := [.character (P.lo (lowerData d e k) (crossedLeftParity d e k)),
          .character (P.hi (lowerData d e k) (crossedLeftParity d e k))]) (post := [])
        (c := P.lo (upperData d e k) 0) (d := P.hi (upperData d e k) 0)
        (ℓ := (upperData d e k).weight.natAbs) rfl)
      (Q.dataDeX _ _ _ _ (crossed_upper_pos d e k))
  apply LinearMap.mem_ker.mp
  change f ∈ LinearMap.ker (Q.quotientMap _ _ _ _
    (crossed_lower_pos d e k) (crossed_upper_pos d e k))
  rw [Q.ker_quotient]
  apply Submodule.mem_sup_right
  rw [← hker]
  exact hD

theorem crossed_cutoffs (hH : 0 < innerWeight d e k) :
    (lowerData d e k).weight.natAbs = d.weight.natAbs + cutoff d e k ∧
    (upperData d e k).weight.natAbs = e.weight.natAbs + cutoff d e k := by
  simp only [lowerData_weight, upperData_weight, Int.natAbs_natCast]
  have hw := RealInducedPairMiddleParity.weight_id d e k
  have hc := Int.toNat_of_nonneg hH.le
  dsimp [cutoff]
  constructor <;> omega

def beforeDescent (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (source d e k) →ₗ[ℂ] KF 4 (crossedPair d e k) :=
  (M.quotient hd he h hH).comp (middleTail h hH)

theorem beforeDescent_exact (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (source d e k) (crossedPair d e k) ⊥
      (beforeDescent hd he h hH) :=
  modulo_comp_bot (M.quotient_exact hd he h hH) (middleTail_exact h hH)

theorem beforeDescent_surjective (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    Function.Surjective (beforeDescent hd he h hH) := by
  intro f
  obtain ⟨g, rfl⟩ := M.quotient_surjective hd he h hH f
  obtain ⟨z, hz⟩ := middleTail_surjective h hH g
  refine ⟨z, ?_⟩
  change M.quotient hd he h hH (middleTail h hH z) = M.quotient hd he h hH g
  rw [hz]

theorem transported_inclusion_coe
    {A B C : Submodule ℂ (Langlands.GeneralLinear 4 ℝ → ℂ)}
    (hAB : A = B) (hBC : B ≤ C) (f : A) :
    (((Submodule.inclusion hBC).comp (LinearEquiv.ofEq A B hAB).toLinearMap) f :
      Langlands.GeneralLinear 4 ℝ → ℂ) = f := rfl

theorem inclusion_coe (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (M.middleList d e k)) :
    (M.inclusion hd he h hH f : Langlands.GeneralLinear 4 ℝ → ℂ) = f :=
  transported_inclusion_coe
    (congrArg (KF 4) (RealInducedPairCrossedMiddleQuotient.middleList_eq hd he h hH).symm)
    (RealInducedPairNegativeInnerQuotient.middle_le (linked hd he)
      (RealInducedPairCrossedMiddleQuotient.crossed_negative hd he hH)) f

theorem inclusion_fourier (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (M.middleList d e k)) (p : ℕ) (j : ℤ) (g : Langlands.GeneralLinear 4 ℝ) :
    blockFourierCoefficient 4 p j (M.inclusion hd he h hH f) g =
      blockFourierCoefficient 4 p j f g :=
  congrArg (fun F : Langlands.GeneralLinear 4 ℝ → ℂ => blockFourierCoefficient 4 p j F g)
    (inclusion_coe hd he h hH f)

theorem beforeDescent_apply (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) (f : KF 4 (source d e k)) :
    beforeDescent hd he h hH f =
      crossedQuotient d e k (M.inclusion hd he h hH (middleTail h hH f)) :=
  LinearMap.congr_fun (mixed_factorization hd he h hH) (middleTail h hH f)

theorem left_generator_low (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (z : KF 4 (Q.Xd d e (M.leftParity d) (M.rightParity d e k))) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
      ((lowerData d e k).weight.natAbs : ℤ) ≤ |j| →
      blockFourierCoefficient 4 0 j (M.inclusion hd he h hH
        (middleTail h hH (Q.qd d e (M.leftParity d) (M.rightParity d e k) z))) g = 0 := by
  intro g hg j hj
  rw [inclusion_fourier]
  rw [(crossed_cutoffs hH).1] at hj
  exact middleTail_low (a := 0) (r := 1) (s := 0) (by decide)
    (Or.inl ⟨rfl, rfl⟩) rfl h hH _
    d.weight.natAbs
    (binomial_low hd (pairParity_eq _ _) (Q.pair_parity _ _) (Q.dataQd _ _ _ _) z)
    g hg j hj

theorem right_generator_low (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (z : KF 4 (Q.Xe d e (M.leftParity d) (M.rightParity d e k))) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
      ((upperData d e k).weight.natAbs : ℤ) ≤ |j| →
      blockFourierCoefficient 4 2 j (M.inclusion hd he h hH
        (middleTail h hH (Q.qe d e (M.leftParity d) (M.rightParity d e k) z))) g = 0 := by
  intro g hg j hj
  rw [inclusion_fourier]
  rw [(crossed_cutoffs hH).2] at hj
  exact middleTail_low (a := 1) (r := 0) (s := 1) (by decide)
    (Or.inr ⟨rfl, rfl⟩) rfl h hH _
    e.weight.natAbs
    (binomial_low he (pairParity_eq _ _) (Q.pair_parity _ _) (Q.dataQe _ _ _ _) z)
    g hg j hj

theorem beforeDescent_qd (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (beforeDescent hd he h hH).comp
      (Q.qd d e (M.leftParity d) (M.rightParity d e k)) = 0 := by
  apply LinearMap.ext
  intro z
  change beforeDescent hd he h hH (Q.qd d e (M.leftParity d) (M.rightParity d e k) z) = 0
  exact (beforeDescent_apply hd he h hH _).trans
    (crossed_zero_left _ (left_generator_low hd he h hH z))

theorem beforeDescent_qe (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (beforeDescent hd he h hH).comp
      (Q.qe d e (M.leftParity d) (M.rightParity d e k)) = 0 := by
  apply LinearMap.ext
  intro z
  change beforeDescent hd he h hH (Q.qe d e (M.leftParity d) (M.rightParity d e k) z) = 0
  exact (beforeDescent_apply hd he h hH _).trans
    (crossed_zero_right _ (right_generator_low hd he h hH z))

def quotient (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 (crossedPair d e k) :=
  (beforeDescent hd he h hH).comp
    (Q.quotientSection d e (M.leftParity d) (M.rightParity d e k) hd he)

theorem quotient_spec (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 [.induced d, .induced e] (crossedPair d e k) ⊥
      (quotient hd he h hH) ∧
    (quotient hd he h hH).comp
      (Q.quotientMap d e (M.leftParity d) (M.rightParity d e k) hd he) =
        beforeDescent hd he h hH ∧
    LinearMap.range (quotient hd he h hH) = LinearMap.range (beforeDescent hd he h hH) :=
  Q.descend d e (M.leftParity d) (M.rightParity d e k) hd he _
    (beforeDescent_exact hd he h hH) (beforeDescent_qd hd he h hH) (beforeDescent_qe hd he h hH)

theorem quotient_surjective (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    Function.Surjective (quotient hd he h hH) := by
  apply LinearMap.range_eq_top.mp
  rw [(quotient_spec hd he h hH).2.2]
  exact LinearMap.range_eq_top.mpr (beforeDescent_surjective hd he h hH)

end RealInducedPairPositiveCrossedQuotient

open RealStandardFiltration RealInducedPairLinkedReplacement
  RealInducedPairCrossedReplacement in
/-- Every positive-inner linked pair has an exact onto quotient with the heavier crossed target. -/
def RealInducedPairPositiveCrossedQuotientStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs → IsLinkedAt d e k →
    0 < innerWeight d e k →
    ∃ T : KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 (crossedPair d e k),
      IsRealIntertwinerModulo 4 [.induced d, .induced e] (crossedPair d e k) ⊥ T ∧
      Function.Surjective T ∧
      IsAdjacentPiece [] [] (.induced d) (.induced e) (crossedPair d e k)

theorem realInducedPairPositiveCrossedQuotient :
    RealInducedPairPositiveCrossedQuotientStatement := by
  intro d e k hd he h hH
  exact ⟨RealInducedPairPositiveCrossedQuotient.quotient hd he h hH,
    (RealInducedPairPositiveCrossedQuotient.quotient_spec hd he h hH).1,
    RealInducedPairPositiveCrossedQuotient.quotient_surjective hd he h hH,
    by simpa using RealInducedPairCrossedReplacement.isAdjacentPiece [] [] h hH⟩

end Langlands.Archimedean
