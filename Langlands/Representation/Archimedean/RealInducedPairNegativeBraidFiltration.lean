import Langlands.Representation.Archimedean.RealFourCharacterResonantWord
import Langlands.Representation.Archimedean.RealInducedPairNegativeExpose
import Langlands.Representation.Archimedean.RealAmbientPolynomialFourierPropagation
import Langlands.Representation.Archimedean.RealIntegralGenericPolynomial
import Langlands.Representation.Archimedean.RealStandardFiltrationQuotientDescent

/-! # The negative-inner filtration from the polynomial braid -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairNegativeBraidFiltration

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockFrobeniusMap
  RealBlockMultiplier RealBlockJacquet RealBlockFourierFinite RealCharacterPair
  RealCharacterPairReducible RealInducedPairLinkedReplacement RealInducedPairAscendingExchange
  RealInducedPairNegativeAscendingWord RealInducedPairNegativeExpose
  RealFourCharacterLongestWord RealFourCharacterResonantWord InductionStages
open RealCanonicalCharacterBraid (Choice)
open RealInducedPairNegativeInnerQuotient (cutoff_bounds)
open RealAmbientCanonicalCharacterBraid (fourier_eqOn eqOn_of_fourier step_eqOn)

variable {d e : ComplexCharacterData} {k : ℕ}
  (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

include hlink hneg in
private theorem outerPositionCharacters :
    realPositionCharacter (outerSource d e k) =
      realPositionCharacter (characters (x d e k) (y d e k) (u d) (v d)) := by
  let O := outerBlock d e k
  have hbase : realPositionCharacter (outerSource d e k) =
      realPositionCharacter (characters (x d e k) (RealCharacterInducedSwap.chA O)
        (RealCharacterInducedSwap.chB O) (v d)) := by
    funext i t
    rw [RealBlockPosition.realPositionCharacter_eq_charFun, RealBlockPosition.realPositionCharacter_eq_charFun]
    rcases i with _ | _ | _ | _ | i <;> rfl
  exact hbase.trans (by rw [chA_outer hlink hneg, chB_outer hlink hneg])

/-- Expand the outer block into its position characters, retaining the function. -/
def outerExpansion (f : KF 4 (outerSource d e k)) : Four (x d e k) (y d e k) (u d) (v d) := by
  refine ⟨(f : Langlands.GeneralLinear 4 ℝ → ℂ), ?_, f.2.2⟩
  have hchars : RealStrictCharacterLanglandsQuotient.IsCharacterList
      (characters (x d e k) (y d e k) (u d) (v d)) := by
    intro b hb
    simp only [characters, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  rw [RealStrictCharacterLanglandsQuotient.realStandardModule_eq hchars,
    ← outerPositionCharacters hlink hneg]
  exact f.2.1.1

theorem outerExpansion_high (f : KF 4 (outerSource d e k))
    (j : ℤ) (hj : Even (j - pairParity (y d e k) (u d))) (hc : |j| ≤ (outerWeight d e k : ℤ))
    (g : Langlands.GeneralLinear 4 ℝ) :
    blockFourierCoefficient 4 1 j (outerExpansion hlink hneg f) g = 0 := by
  have hj' : Even (j - pairParity (u d) (y d e k)) := by
    rw [RealInducedSwapGeneric.pairParity_comm (u d) (y d e k)]
    exact hj
  have hlt := abs_lt_of_parity (outer_parity hneg) hj' hc
  change blockFourierCoefficient 4 1 j f g = 0
  apply f.2.1.2 1 (outerBlock d e k) rfl j _ g
  simp only [outerBlock, pairInduced_weight, abs_of_nonneg (Int.natCast_nonneg _)]
  exact hlt

private def exposingGeneric (d e : ComplexCharacterData) (k : ℕ)
    (hneg : innerWeight d e k < 0) : Choice (pairParity (x d e k) (u d)) :=
  .generic (leftGap d e k : ℂ)
    (fun i => genericSeq_denom_ne_zero
      (by simpa using (show (0 : ℝ) < leftGap d e k by exact_mod_cast (gap_bounds hneg).1))
      (RealCharacterInducedPushforward.pairParity_nonneg _ _) i)

private theorem expose_eqOn (rM : ℕ)
    (hM : e.weight.natAbs = resonantWeight (pairParity (x d e k) (y d e k)) rM)
    (f : KF 4 (outerSource d e k)) :
    Set.EqOn (expose hlink hneg f : Langlands.GeneralLinear 4 ℝ → ℂ)
      (swap1 (exposingGeneric d e k hneg) (swap0 (.tail rM) (outerExpansion hlink hneg f)) :
        Langlands.GeneralLinear 4 ℝ → ℂ) (unitaryCompact ℝ 4) := by
  obtain ⟨h₀, h₁, hformula⟩ := expose_forward_formula hlink hneg
  let C₀ : Choice (pairParity (x d e k) (y d e k)) := .tail rM
  let C₁ := exposingGeneric d e k hneg
  have hcut : (outerBlock d e k).weight.natAbs - leftGap d e k = e.weight.natAbs := by
    change outerWeight d e k - leftGap d e k = e.weight.natAbs
    have hp := (gaps_add hneg).2.2.1
    omega
  have hμ₀ : tailMultiplier ((outerBlock d e k).weight.natAbs - leftGap d e k)
        (pairParity (x d e k) (RealCharacterInducedSwap.chA (outerBlock d e k)))
        (sigma0 (x d e k) (RealCharacterInducedSwap.chA (outerBlock d e k))) = C₀.multiplier := by
    rw [chA_outer hlink hneg, hcut, hM]
    rfl
  have hμ₁ : genericMultiplier (leftGap d e k : ℂ)
        (pairParity (RealCharacterInducedSwap.chB (outerBlock d e k)) (x d e k)) = C₁.multiplier := by
    rw [chB_outer hlink hneg, RealInducedSwapGeneric.pairParity_comm (u d) (x d e k)]
    rfl
  let ds₀ := RealCanonicalCharacterBraid.data (n := 3) (pre := []) (post := [.character (u d)]) rfl C₀
  let ds₁ := RealCanonicalCharacterBraid.data (n := 3) (pre := [.character (y d e k)]) (post := []) rfl C₁
  intro g hg
  let κ : unitaryCompact ℝ 4 := ⟨g, hg⟩
  let F := outerExpansion hlink hneg f
  let S := RealAmbientCanonicalCharacterBraid.sliceTriple
    (pre := []) (post := [.character (v d)]) (a := x d e k) (b := y d e k) (c := u d)
    (by decide : realRank [] + 3 ≤ 4) κ F
  have hS : Set.EqOn (sourceSlice κ f : Langlands.GeneralLinear 3 ℝ → ℂ) S (unitaryCompact ℝ 3) :=
    fun _ _ => rfl
  let f₀ := blockFrobMap h₀ (sourceSlice κ f)
  let f₁ := blockFrobMap h₁ f₀
  have he₀ : Set.EqOn (f₀ : Langlands.GeneralLinear 3 ℝ → ℂ)
      (blockFrobMap ds₀ S : Langlands.GeneralLinear 3 ℝ → ℂ) (unitaryCompact ℝ 3) :=
    step_eqOn ds₀ S _ _ (continuous_coe f₀) f₀.2.2 hS (fun j a ha => by
      change blockFourierCoefficient 3 0 j (blockFrobMap h₀ (sourceSlice κ f)) a =
        C₀.multiplier j * blockFourierCoefficient 3 0 j (sourceSlice κ f) a
      rw [blockFourierCoefficient_blockFrobMap h₀ _ ha, hμ₀])
  have he₁ : Set.EqOn (f₁ : Langlands.GeneralLinear 3 ℝ → ℂ)
      (blockFrobMap ds₁ (blockFrobMap ds₀ S) : Langlands.GeneralLinear 3 ℝ → ℂ) (unitaryCompact ℝ 3) :=
    step_eqOn ds₁ (blockFrobMap ds₀ S) _ _ (continuous_coe f₁) f₁.2.2 he₀ (fun j a ha => by
      change blockFourierCoefficient 3 1 j (blockFrobMap h₁ f₀) a =
        C₁.multiplier j * blockFourierCoefficient 3 1 j f₀ a
      rw [blockFourierCoefficient_blockFrobMap h₁ _ ha, hμ₁])
  have hs₀ := RealAmbientCanonicalCharacterBraid.slice_swap0 (n := 4)
    (pre := []) (post := [.character (v d)]) (c := u d) rfl C₀
    (by decide : realRank [] + 3 ≤ 4) κ F
  have hs₁ := RealAmbientCanonicalCharacterBraid.slice_swap1 (n := 4)
    (pre := []) (post := [.character (v d)]) (a := y d e k) rfl C₁
    (by decide : realRank [] + 3 ≤ 4) κ (swap0 C₀ F)
  have hslice : RealAmbientCanonicalCharacterBraid.sliceTriple
      (pre := []) (post := [.character (v d)]) (by decide : realRank [] + 3 ≤ 4)
      κ (swap1 C₁ (swap0 C₀ F)) = blockFrobMap ds₁ (blockFrobMap ds₀ S) :=
    hs₁.trans (congrArg (blockFrobMap ds₁) hs₀)
  change (expose hlink hneg f : Langlands.GeneralLinear 4 ℝ → ℂ) κ =
    (swap1 C₁ (swap0 C₀ F) : Langlands.GeneralLinear 4 ℝ → ℂ) κ
  calc
    _ = (exposedSlice κ (expose hlink hneg f) : Langlands.GeneralLinear 3 ℝ → ℂ) 1 :=
      (sliceK_apply_one _ _ _ κ _).symm
    _ = (f₁ : Langlands.GeneralLinear 3 ℝ → ℂ) 1 := congrFun (hformula κ f) 1
    _ = (blockFrobMap ds₁ (blockFrobMap ds₀ S) : Langlands.GeneralLinear 3 ℝ → ℂ) 1 :=
      he₁ (one_mem _)
    _ = _ := (congrFun (congrArg Subtype.val hslice) 1).symm.trans
      (sliceK_apply_one _ _ _ κ _)

private theorem tail_parameter {ε : ℤ} {ℓ r : ℕ} (hε : ε = 0 ∨ ε = 1)
    (h : ℓ = resonantWeight ε r) : (Choice.tail r : Choice ε).parameter = -(ℓ : ℂ) := by
  have hc : (ε.toNat : ℤ) = ε := Int.toNat_of_nonneg (by omega)
  have hc' : (ε.toNat : ℂ) = ε := by exact_mod_cast hc
  rw [Choice.parameter, RealClearedCompactDegeneration.pole, h]
  unfold resonantWeight
  push_cast
  rw [hc']

open RealTailMultiplierPolynomial in
private theorem first_two_zero (rM rL : ℕ)
    (hM : e.weight.natAbs = resonantWeight (pairParity (x d e k) (y d e k)) rM)
    (hL : d.weight.natAbs = resonantWeight (pairParity (u d) (v d)) rL)
    (f : KF 4 (outerSource d e k)) (hf : replacementQuotient hlink hneg f = 0) :
    swap2 (.tail rL) (swap0 (.tail rM) (outerExpansion hlink hneg f)) = 0 := by
  let G := swap0 (.tail rM) (outerExpansion hlink hneg f)
  let C := exposingGeneric d e k hneg
  let hdata : IsBlockFrobData 4
      (characters (y d e k) (x d e k) (u d) (v d))
      (characters (y d e k) (u d) (x d e k) (v d)) 1
      (pairParity (x d e k) (u d)) ((-1 : ℂ) ^ (pairParity (x d e k) (u d)).natAbs)
      (genericMultiplier (leftGap d e k : ℂ) (pairParity (x d e k) (u d))) :=
    RealCanonicalCharacterBraid.data (n := 4) (pre := [.character (y d e k)])
      (post := [.character (v d)]) rfl C
  let F := blockFrobMap hdata G
  have hE : Set.EqOn (expose hlink hneg f : Langlands.GeneralLinear 4 ℝ → ℂ) F (unitaryCompact ℝ 4) :=
    expose_eqOn hlink hneg rM hM f
  have hp : Even ((leftGap d e k : ℤ) - pairParity (x d e k) (u d)) := left_parity
  let Q := tailPolynomial (leftGap d e k)
  let c := Q.eval (pairParity (x d e k) (u d) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c, Q]
    apply RealIntegralGenericPolynomial.polynomial_ne_zero
    obtain ⟨a, ha⟩ := hp
    exact ⟨-a, by omega⟩
  have hμ : ∀ j : ℤ, ∀ g ∈ unitaryCompact ℝ 4,
      blockFourierCoefficient 4 1 j (c • G) g =
        Q.eval (j : ℂ) * blockFourierCoefficient 4 1 j F g := by
    intro j g hg
    rw [blockFourierCoefficient_smul]
    exact (RealIntegralGenericPolynomial.generic_frob_relation (gap_bounds hneg).1
      (pairParity_eq _ _) hp hdata G j hg).symm
  have hlow : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (innerCutoff d e k : ℤ) ≤ |j| →
      blockFourierCoefficient 4 2 j F g = 0 := by
    intro g hg j hj
    rw [← fourier_eqOn hE j hg]
    exact (replacementQuotient_eq_zero hlink hneg f).mp hf g hg j hj
  have hprop := RealAmbientPolynomialFourierPropagation.propagation 1
    (by decide : 1 + 3 ≤ 4) (r := 0) (s := 1) (Or.inr ⟨rfl, rfl⟩)
    (continuous_coe F) (continuous_coe (c • G)) F.2.2 (c • G).2.2
    Q hμ (innerCutoff d e k) hlow
  have hsum : innerCutoff d e k + Q.natDegree = d.weight.natAbs := by
    rw [show Q.natDegree = leftGap d e k from tailPolynomial_natDegree _]
    exact (Nat.add_comm _ _).trans (gaps_add hneg).1
  let D : IsBlockFrobData 4 (characters (y d e k) (x d e k) (u d) (v d))
      (characters (y d e k) (x d e k) (v d) (u d)) 2
      (pairParity (u d) (v d)) ((-1 : ℂ) ^ (pairParity (u d) (v d)).natAbs)
      (tailMultiplier (resonantWeight (pairParity (u d) (v d)) rL)
        (pairParity (u d) (v d)) ((-1 : ℂ) ^ (pairParity (u d) (v d)).natAbs)) :=
    RealCanonicalCharacterBraid.data (n := 4) (pre := [.character (y d e k), .character (x d e k)])
      (post := []) rfl (.tail rL)
  have hpL : 0 < resonantWeight (pairParity (u d) (v d)) rL := hL ▸ leftWeight_pos hneg
  have heL : Even ((resonantWeight (pairParity (u d) (v d)) rL : ℤ) - 1 - pairParity (u d) (v d)) := by
    rw [← hL]
    exact RealInducedPairQuotientPresentation.pair_parity d 0
  change blockFrobMap D G = 0
  apply (RealInducedPairOuterTail.tail_eq_zero_iff hpL (pairParity_eq _ _) heL
    (neg_one_pow_sq _) D G).mpr
  intro g hg j hj
  have hg0 := hprop g hg j (by rwa [hsum, hL])
  change blockFourierCoefficient 4 2 j
    (c • (G : Langlands.GeneralLinear 4 ℝ → ℂ)) g = 0 at hg0
  rw [blockFourierCoefficient_smul] at hg0
  exact (mul_eq_zero.mp hg0).resolve_left hc

private theorem sigma_lower_even (b : RealCharacterData) :
    sigma0 (u d) b = (-1 : ℂ) ^ b.parity.val := by
  rw [sigma0_eq, u_parity, Fin.val_zero, pow_zero, one_mul]

private theorem outerSection_eq (rP : ℕ)
    (hP : outerWeight d e k = resonantWeight (pairParity (y d e k) (u d)) rP)
    (f : KF 4 (outerSource d e k)) :
    blockFrobMap (inverseTailData rP) (outerExpansion hlink hneg f) =
      RealInducedPairDistantParity.outerSection hlink (outer_parity hneg) f := by
  change outerWeight d e k = (pairParity (y d e k) (u d)).toNat + 2 * rP + 1 at hP
  let sec := data_q1 (n := 4) (pre := [.character (x d e k)]) (post := [.character (v d)])
    rfl (RealInducedPairOuterTail.outerWeight_pos d e k) (outer_parity hneg) (gaps hlink hneg).1
  apply eq_of_blockFourierCoefficient_eq (p := 1) (by decide)
  intro j g hg
  calc
    _ = (((Choice.tail rP : Choice (pairParity (y d e k) (u d))).multiplier j)⁻¹) *
        blockFourierCoefficient 4 1 j (outerExpansion hlink hneg f) g :=
      blockFourierCoefficient_blockFrobMap (inverseTailData rP) _ hg j
    _ = (tailMultiplier (outerWeight d e k) (pairParity (u d) (y d e k))
          ((-1 : ℂ) ^ (y d e k).parity.val) j)⁻¹ * blockFourierCoefficient 4 1 j f g := by
      rw [Choice.multiplier, ← hP, RealInducedSwapGeneric.pairParity_comm (y d e k) (u d)]
      change (tailMultiplier (outerWeight d e k) (pairParity (u d) (y d e k))
          (sigma0 (u d) (y d e k)) j)⁻¹ * _ = _
      rw [sigma_lower_even]
      rfl
    _ = _ := (blockFourierCoefficient_blockFrobMap sec f hg j).symm

private theorem innerSwap_eq (s : ℕ)
    (hs : innerCutoff d e k = resonantWeight (pairParity (x d e k) (v d)) s)
    (f : KF 4 (X1 d e 0 (rightParity d e k))) :
    innerSwap hlink hneg f = swap1 (.tail s) f := by
  change innerCutoff d e k = (pairParity (x d e k) (v d)).toNat + 2 * s + 1 at hs
  let A := RealCanonicalCharacterBraid.data (n := 4) (pre := [.character (u d)])
    (post := [.character (y d e k)]) rfl (.tail s : Choice (pairParity (x d e k) (v d)))
  apply eq_of_blockFourierCoefficient_eq (p := 1) (by decide)
  intro j g hg
  calc
    _ = innerMultiplier d e k j * blockFourierCoefficient 4 1 j f g :=
      blockFourierCoefficient_blockFrobMap (incomingData hlink hneg).data3 f hg j
    _ = _ := by
      change _ = blockFourierCoefficient 4 1 j (blockFrobMap A f) g
      rw [show innerMultiplier d e k =
        (Choice.tail s : Choice (pairParity (x d e k) (v d))).multiplier by rw [Choice.multiplier, ← hs]]
      exact (blockFourierCoefficient_blockFrobMap A f hg j).symm

private theorem quotient_eq_zero_of_canonical (rM rL : ℕ)
    (hM : e.weight.natAbs = resonantWeight (pairParity (x d e k) (y d e k)) rM)
    (hL : d.weight.natAbs = resonantWeight (pairParity (u d) (v d)) rL)
    (F : KF 4 (P.X d e 0 (rightParity d e k)))
    (hF : swap2 (.tail rM) (swap0 (.tail rL) F) = 0) :
    quotientMap hneg F = 0 := by
  let CL : Choice (pairParity (u d) (v d)) := .tail rL
  let CM : Choice (pairParity (x d e k) (y d e k)) := .tail rM
  let A := RealCanonicalCharacterBraid.data (n := 4) (pre := [])
    (post := [.character (x d e k), .character (y d e k)]) rfl CL
  let B := RealCanonicalCharacterBraid.data (n := 4)
    (pre := [.character (v d), .character (u d)]) (post := []) rfl CM
  let G := swap0 CL F
  let D := P.Dd d e 0 (rightParity d e k) (leftWeight_pos hneg) F
  have hDG : Set.EqOn (D : Langlands.GeneralLinear 4 ℝ → ℂ) G (unitaryCompact ℝ 4) := by
    apply eqOn_of_fourier (p := 0) (by decide) (continuous_coe D) (continuous_coe G) D.2.2 G.2.2
    intro j g hg
    calc
      _ = tailMultiplier d.weight.natAbs (pairParity (u d) (v d)) ((-1 : ℂ) ^ (v d).parity.val) j *
          blockFourierCoefficient 4 0 j F g :=
        blockFourierCoefficient_blockFrobMap (P.dataDd d e 0 (rightParity d e k) (leftWeight_pos hneg))
          F hg j
      _ = CL.multiplier j * blockFourierCoefficient 4 0 j F g := by
        rw [← sigma_lower_even (d := d) (v d), hL]
        rfl
      _ = _ := (blockFourierCoefficient_blockFrobMap A F hg j).symm
  have hMpar : Even ((resonantWeight (pairParity (x d e k) (y d e k)) rM : ℤ) - 1 -
      pairParity (x d e k) (y d e k)) := by
    rw [← hM]
    exact RealInducedPairQuotientPresentation.pair_parity e (rightParity d e k)
  have hMb : 0 < resonantWeight (pairParity (x d e k) (y d e k)) rM := by
    rw [← hM]
    exact rightWeight_pos hneg
  have hG := (RealInducedPairOuterTail.tail_eq_zero_iff hMb (pairParity_eq _ _)
    hMpar (neg_one_pow_sq _) B G).mp hF
  have hDe : P.De d e 0 (rightParity d e k) (rightWeight_pos hneg) D = 0 := by
    apply (RealInducedPairOuterTail.tail_eq_zero_iff (rightWeight_pos hneg) (pairParity_eq _ _)
      (RealInducedPairQuotientPresentation.pair_parity e (rightParity d e k)) (neg_one_pow_sq_fin _)
      (P.dataDe d e 0 (rightParity d e k) (rightWeight_pos hneg)) D).mpr
    intro g hg j hj
    exact (fourier_eqOn hDG j hg).trans (hG g hg j (by simpa only [← hM] using hj))
  change ofEqMap (RealInducedPairQuotientPresentation.KF_Z d e 0 (rightParity d e k))
    (P.De d e 0 (rightParity d e k) (rightWeight_pos hneg) D) = 0
  rw [hDe, map_zero]

/-- The negative-inner mixed map kills the actual replacement quotient's kernel. -/
theorem mixedMap_eq_zero
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b)
    (f : KF 4 (outerSource d e k)) (hf : replacementQuotient hlink hneg f = 0) :
    mixedMap hlink hneg f = 0 := by
  have hpP : Even ((outerWeight d e k : ℤ) - 1 - pairParity (y d e k) (u d)) := by
    rw [RealInducedSwapGeneric.pairParity_comm (y d e k) (u d)]
    exact outer_parity hneg
  obtain ⟨r, hr, _⟩ := exists_half (RealInducedPairOuterTail.outerWeight_pos d e k)
    (pairParity_eq (y d e k) (u d)) hpP
  obtain ⟨s, hs, _⟩ := exists_half (cutoff_bounds hneg).1
    (pairParity_eq (x d e k) (v d)) (inner_parity hneg)
  obtain ⟨rM, hM, _⟩ := exists_half (rightWeight_pos hneg)
    (pairParity_eq (x d e k) (y d e k))
    (RealInducedPairQuotientPresentation.pair_parity e (rightParity d e k))
  obtain ⟨rL, hL, _⟩ := exists_half (leftWeight_pos hneg)
    (pairParity_eq (u d) (v d)) (RealInducedPairQuotientPresentation.pair_parity d 0)
  change outerWeight d e k = resonantWeight (pairParity (y d e k) (u d)) r at hr
  change innerCutoff d e k = resonantWeight (pairParity (x d e k) (v d)) s at hs
  let Cxy : Choice (pairParity (x d e k) (y d e k)) := .tail rM
  let Cuv : Choice (pairParity (u d) (v d)) := .tail rL
  have hxy := tail_parameter (pairParity_eq (x d e k) (y d e k)) hM
  have huv := tail_parameter (pairParity_eq (u d) (v d)) hL
  have hAL : (leftGap d e k : ℂ) + (innerCutoff d e k : ℂ) = d.weight.natAbs := by
    exact_mod_cast (gaps_add hneg).1
  have hBM : (rightGap d e k : ℂ) + (innerCutoff d e k : ℂ) = e.weight.natAbs := by
    exact_mod_cast (gaps_add hneg).2.1
  have hAP : (leftGap d e k : ℂ) + (e.weight.natAbs : ℂ) = outerWeight d e k := by
    exact_mod_cast (gaps_add hneg).2.2.1
  have hBP : (rightGap d e k : ℂ) + (d.weight.natAbs : ℂ) = outerWeight d e k := by
    exact_mod_cast (gaps_add hneg).2.2.2
  let F := outerExpansion hlink hneg f
  have hz := specializedWord_eq_zero hPoly r s (gap_bounds hneg).1 (gap_bounds hneg).2 Cxy Cuv
    (by
      change (leftGap d e k : ℂ) =
        (Choice.tail rM : Choice (pairParity (x d e k) (y d e k))).parameter +
          (resonantWeight (pairParity (y d e k) (u d)) r : ℂ)
      rw [hxy, ← hr]
      linear_combination hAP)
    (by
      change -(resonantWeight (pairParity (x d e k) (v d)) s : ℂ) =
        (Choice.tail rM : Choice (pairParity (x d e k) (y d e k))).parameter + (rightGap d e k : ℂ)
      rw [hxy, ← hs]
      linear_combination -hBM)
    (by
      change -(resonantWeight (pairParity (x d e k) (v d)) s : ℂ) =
        (leftGap d e k : ℂ) + (Choice.tail rL : Choice (pairParity (u d) (v d))).parameter
      rw [huv, ← hs]
      linear_combination -hAL)
    (by
      change (rightGap d e k : ℂ) = (resonantWeight (pairParity (y d e k) (u d)) r : ℂ) +
        (Choice.tail rL : Choice (pairParity (u d) (v d))).parameter
      rw [huv, ← hr]
      linear_combination hBP)
    F (fun j hj hcap g _ => outerExpansion_high hlink hneg f j hj (by simpa only [← hr] using hcap) g)
    (first_two_zero hlink hneg rM rL hM hL f hf)
  let S := RealInducedPairDistantParity.outerSection hlink (outer_parity hneg) f
  have hS : blockFrobMap (inverseTailData r) F = S := outerSection_eq hlink hneg r hr f
  have hG : blockFrobMap (rightData (rightGap d e k) 0)
        (blockFrobMap (leftData (leftGap d e k) 0) S) = middleSwap hlink hneg S := rfl
  rw [hS, hG, ← innerSwap_eq hlink hneg s hs] at hz
  exact quotient_eq_zero_of_canonical hneg rM rL hM hL _ hz

include hlink hneg in
/-- The full negative-inner filtration assuming the compact polynomial braid. -/
theorem filtration
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  have hker : (LinearMap.ker (replacementQuotient hlink hneg)).map (mixedMap hlink hneg) ≤
      LinearMap.range (swapMap hlink hneg) := by
    rintro z ⟨f, hf, rfl⟩
    rw [mixedMap_eq_zero hlink hneg hPoly f (LinearMap.mem_ker.mp hf)]
    exact Submodule.zero_mem _
  obtain ⟨q, hq, hrange⟩ := exists_quotient_descent (mixedMap_modulo hlink hneg)
    (replacementQuotient_exact hlink hneg) (replacementQuotient_surjective hlink hneg) hker
  apply (realAdjacentFiltration_iff 4 [] [] (.induced d) (.induced e)).mpr
  apply RealCharacterInducedPushforward.hasFiltration_two
    (P := IsAdjacentPiece [] [] (.induced d) (.induced e))
    (by exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩)
    (RealInducedPairLinkedReplacement.isAdjacentPiece [] [] hlink)
    (swapMap hlink hneg) q (swapMap_exact hlink hneg) hq
  intro z
  have hz : z ∈ LinearMap.range (swapMap hlink hneg) ⊔ LinearMap.range q := by
    rw [hrange]
    obtain ⟨a, b, rfl⟩ := maps_span hlink hneg z
    exact add_mem (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right ⟨b, rfl⟩)
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hz
  exact ⟨a, b, hab⟩

end Langlands.Archimedean.RealInducedPairNegativeBraidFiltration

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement
  RealInducedPairNegativeAscendingWord RealInducedPairNegativeExpose
  RealInducedPairNegativeBraidFiltration

/-- With the full compact polynomial braid, the mixed map descends to the
replacement quotient and gives the linked negative-inner filtration. -/
def RealInducedPairNegativeBraidFiltrationStatement : Prop :=
  (∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b) →
    ∀ (d e : ComplexCharacterData) (k : ℕ) (hlink : IsLinkedAt d e k)
      (hneg : innerWeight d e k < 0),
      (∀ f, replacementQuotient hlink hneg f = 0 → mixedMap hlink hneg f = 0) ∧
      RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairNegativeBraidFiltration : RealInducedPairNegativeBraidFiltrationStatement :=
  fun hPoly _ _ _ hlink hneg =>
    ⟨mixedMap_eq_zero hlink hneg hPoly, filtration hlink hneg hPoly⟩

end Langlands.Archimedean
