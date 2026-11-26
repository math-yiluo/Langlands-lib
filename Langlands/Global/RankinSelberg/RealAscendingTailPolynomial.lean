import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealTaylorLeftPolynomialProof

/-! # Lower-root polynomiality in the kernel of a real ascending tail -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

attribute [local instance 100] LieRing.ofAssociativeRing

open RealBlockPosition RealBlockFrobeniusMap RealBlockMultiplier RealBlockJacquet RealBlockRotation
open RealCharacterPair RealCharacterPairReducible RealLinkedJacquetFunctional RealJacquetFrobenius
open RealCharacterCrossing (blockJacquet_pow_eq_zero)
open RealInducedCharacter

private theorem blockFrobMap_polynomial {n p k : ℕ} {ds es : List RealBlock}
    {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}
    (h : IsBlockFrobData n ds es p ε σ μ)
    (hRec : IsRecurrent (GramFormula.realPositionExponent ds p -
      GramFormula.realPositionExponent ds (p + 1) + 1) ε μ)
    (hk : 0 < k)
    (hExp : GramFormula.realPositionExponent es (p + 1) -
      GramFormula.realPositionExponent es p = (k : ℂ))
    (hModes : ∀ (j : ℤ) (f : RealStandardFiltration.KF n ds),
      μ j * blockFourierCoefficient n p j f 1 ≠ 0 →
        |j| < (k : ℤ) ∧ Even ((k : ℤ) - 1 - j))
    (v : RealStandardFiltration.KF n ds) (g : Langlands.GeneralLinear n ℝ) :
    ∃ q : Polynomial ℂ, q.degree < k ∧ ∀ t : ℝ,
      (blockFrobMap h v : Langlands.GeneralLinear n ℝ → ℂ)
        (lowerRootElement n p h.lt t * g) = q.eval (t : ℂ) := by
  let α := shiftedExponent n es
  let e := positionSign n es
  have hGap : α (ia h.lt) - α (ib h.lt) = 1 - (k : ℂ) := by
    dsimp only [α, shiftedExponent, ia, ib]
    push_cast
    linear_combination -hExp
  have hχ (x : ℝˣ) (hx : 0 < (x : ℝ)) :
      posChar α e (p + 1) x = ((x : ℝ) : ℂ) ^ k * posChar α e p x := by
    have he : expo α (ib h.lt) = expo α (ia h.lt) + (k : ℂ) := by
      simp only [expo, ia, ib]
      simp only [ia, ib] at hGap
      push_cast
      linear_combination -hGap
    rw [show posChar α e (p + 1) x = charFun (e (ib h.lt)) (expo α (ib h.lt)) x from
      posChar_apply α e (ib h.lt) x,
      show posChar α e p x = charFun (e (ia h.lt)) (expo α (ia h.lt)) x from
        posChar_apply α e (ia h.lt) x,
      charFun_of_pos _ _ hx, charFun_of_pos _ _ hx, he,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_natCast, mul_comm]
  have hPS : (blockFrobMap h v : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n (posChar α e) := by
    rw [show principalSeries ℝ n (posChar α e) =
      principalSeries ℝ n (realPositionCharacter es) from principalSeries_posChar_shiftedExponent n es]
    exact (blockFrobMap h v).property.1.1
  apply realTaylorLeftPolynomial n (posChar α e) p k h.lt hχ _ hPS _ g
  intro κ hκ
  have hJ := h.isRealJacquetFunctional hRec
  have hGK := isRealGKModule_realStandardModule n ds
  rw [blockFrobMap_apply_coe,
    ← frobFun_rightTranslation h.hsign ⟨κ, hκ⟩ v,
    iterate_rightDerivative_frobFun hGK hJ, frobFun_apply_one h.hsign]
  exact blockJacquet_pow_eq_zero h.lt hJ hk hGap hModes _

/-- Functions in the kernel of a nonzero-weight ascending tail are polynomial along the
lower root inside that block, of degree less than its absolute weight. -/
theorem ascendingTailKernel_polynomial {n : ℕ} {pre post : List RealBlock}
    {d : ComplexCharacterData} {sa sb : Fin 2}
    (hn : realRank (pre ++ [.induced d] ++ post) = n) (hl : 0 < d.weight.natAbs)
    (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    (f : RealStandardFiltration.KF n
      (pre ++ [.character (cb d sb), .character (ca d sa)] ++ post))
    (hf : f ∈ LinearMap.ker (blockFrobMap (data_tail hn hl hs)))
    (g : Langlands.GeneralLinear n ℝ) :
    ∃ q : Polynomial ℂ, q.degree < d.weight.natAbs ∧ ∀ t : ℝ,
      (f : Langlands.GeneralLinear n ℝ → ℂ)
        (lowerRootElement n (realRank pre) (data_tail hn hl hs).lt t * g) =
        q.eval (t : ℂ) := by
  let c := cb d sb
  let c' := ca d sa
  let ε := pairParity c c'
  let k := d.weight.natAbs
  let src := pre ++ [RealBlock.character c, .character c'] ++ post
  let swp := pre ++ dc c c' ++ post
  have hSrc : pre ++ .character c :: .character c' :: post = src := by
    simp [src, List.append_assoc]
  have hε : ε = 0 ∨ ε = 1 := pairParity_eq _ _
  have hPar : Even ((k : ℤ) - 1 - ε) := tail_parity hs
  have hRank : realRank (pre ++ .character c :: .character c' :: post) = n := by
    rw [hSrc]
    exact realRank_tail_mid (sa := sa) (sb := sb) hn
  have h0 : IsBlockFrobData n swp src (realRank pre) ε (sigma0 c c')
      (binomialMultiplier k ε) := by
    rw [← hSrc]
    exact data_q0 (ℓ := k) hRank
  have hInv : IsBlockFrobData n src swp (realRank pre) ε (sigma0 c c')⁻¹
      (fun j => (binomialMultiplier k ε j)⁻¹) := by
    rw [← hSrc]
    exact data_B (ℓ := k) hRank
  have hKer : LinearMap.ker (blockFrobMap (data_tail hn hl hs)) ≤
      LinearMap.range (blockFrobMap h0) := by
    apply ker_le_range h0 hInv (data_tail hn hl hs)
    intro j hj hprod
    have hbin : binomialMultiplier k ε j = 0 := by
      by_contra hz
      exact hprod (mul_inv_cancel₀ hz)
    have hle : (k : ℤ) ≤ |j| := le_of_not_gt fun hjlt =>
      (binomialMultiplier_ne_zero_iff hl hε hPar hj).mpr hjlt hbin
    have hlt : (k : ℤ) < |j| := by
      rcases hle.lt_or_eq with hb | hb
      · exact hb
      · exact False.elim (not_lt_of_ge hle (abs_lt_of_parity hPar hj hb.symm.le))
    exact (tailMultiplier_ne_zero_iff hl hε hPar (neg_one_pow_sq_fin sa) hj).mpr hlt
  obtain ⟨v, rfl⟩ := hKer hf
  have hExp : c'.exponent - c.exponent = (k : ℂ) := aExp_sub_bExp d
  have hRec : IsRecurrent
      (GramFormula.realPositionExponent (pre ++ dc c c' ++ post) (realRank pre) -
        GramFormula.realPositionExponent (pre ++ dc c c' ++ post) (realRank pre + 1) + 1)
      ε (binomialMultiplier k ε) := by
    rw [exponent_swp_zero, exponent_swp_one, hExp]
    exact isRecurrent_binomialMultiplier hl hε hPar
  have hPos : GramFormula.realPositionExponent src (realRank pre + 1) -
      GramFormula.realPositionExponent src (realRank pre) = (k : ℂ) := by
    rw [h0.exp_q, h0.exp_p]
    change GramFormula.realPositionExponent (pre ++ dc c c' ++ post) (realRank pre) -
      GramFormula.realPositionExponent (pre ++ dc c c' ++ post) (realRank pre + 1) = (k : ℂ)
    rw [exponent_swp_zero, exponent_swp_one, hExp]
  have hModes (j : ℤ) (f' : RealStandardFiltration.KF n swp)
      (hj : binomialMultiplier k ε j * blockFourierCoefficient n (realRank pre) j f' 1 ≠ 0) :
      |j| < (k : ℤ) ∧ Even ((k : ℤ) - 1 - j) := by
    have hjPar : Even (j - ε) := by
      by_contra hne
      exact hj (by rw [blockFourierCoefficient_eq_zero_of_not_even h0.lt h0.par f' hne, mul_zero])
    exact ⟨(binomialMultiplier_ne_zero_iff hl hε hPar hjPar).mp (left_ne_zero_of_mul hj), by
      obtain ⟨x, hx⟩ := hPar
      obtain ⟨y, hy⟩ := hjPar
      exact ⟨x - y, by omega⟩⟩
  exact blockFrobMap_polynomial h0 hRec hl hPos hModes v g

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
