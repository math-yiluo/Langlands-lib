import Langlands.Global.RankinSelberg.RealEqualPolynomialGeneration
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Global.RankinSelberg.RealPositionPairPolynomial
import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Polynomial ordinary normalizations from real character presentations -/

noncomputable section

open Set Polynomial
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealPrincipalSeries RealBlockParameters
open RealEqualPolynomialGeneration (GaussianEqualTest gaussianEqualIntegral)
open RealJacquet (IsRealCharacterList)
open Langlands.Archimedean.RealJacquetFrobenius (charData)
open Langlands.Archimedean (characterOfParams)

private def blockShape : RealBlock → Shape
  | .character c => .inl c.parity
  | .induced d => .inr d.weight

private def blockExponent : RealBlock → ℂ
  | .character c => c.exponent
  | .induced d => d.exponent

private theorem blockOfParams_blockShape (d : RealBlock) : blockOfParams (blockShape d) (blockExponent d) = d := by
  cases d with
  | character c =>
    change RealBlock.character (charData c.parity c.exponent) = .character c
    exact congrArg RealBlock.character (realCharacterData_ext rfl rfl)
  | induced c =>
    change RealBlock.induced (characterOfParams c.weight c.exponent) = .induced c
    exact congrArg RealBlock.induced (complexCharacterData_ext rfl rfl)

private theorem blockList_shape (ds : List RealBlock) :
    blockList (fun i : Fin ds.length => blockShape (ds.get i)) (fun i => blockExponent (ds.get i)) = ds := by
  unfold blockList
  simp only [blockOfParams_blockShape, List.ofFn_get]

private def shiftPolynomial (l : List ℂ) (z : ℂ) : Polynomial ℂ :=
  (l.map fun b => (X + C (z + b)) * C (2 * (Real.pi : ℂ))⁻¹).prod

private theorem eval_shiftPolynomial (l : List ℂ) (z s : ℂ) :
    (shiftPolynomial l z).eval s = shiftProduct l (s + z) := by
  induction l with
  | nil => simp [shiftPolynomial, shiftProduct]
  | cons b l ih =>
    simp only [shiftPolynomial, shiftProduct, List.map_cons, List.prod_cons, eval_mul, eval_add, eval_X, eval_C]
    rw [← add_assoc, ← div_eq_mul_inv]
    exact congrArg ((s + z + b) / (2 * (Real.pi : ℂ)) * ·) ih

local notation "L[" ds "," es "]" => realPairLFactor ds es

/-- The position factor comparison, with an actual nonzero polynomial in the spectral variable. -/
theorem exists_expandPairDenominatorPolynomial (ds es : List RealBlock) :
    ∃ R : Polynomial ℂ, R ≠ 0 ∧ ∀ s, L[expand ds, expand es].denominator s = R.eval s * L[ds, es].denominator s := by
  classical
  obtain ⟨shifts, hShifts⟩ := realPositionPairPolynomial
  let d (i : Fin ds.length) := blockShape (ds.get i)
  let e (j : Fin es.length) := blockShape (es.get j)
  let p (i : Fin ds.length) := blockExponent (ds.get i)
  let q (j : Fin es.length) := blockExponent (es.get j)
  let R := ∏ i, ∏ j, shiftPolynomial (shifts (d i) (e j)) (p i + q j)
  have hR (s : ℂ) : L[expand ds, expand es].denominator s = R.eval s * L[ds, es].denominator s := by
    have h := hShifts d e p q s
    rw [show blockList d p = ds from blockList_shape ds, show blockList e q = es from blockList_shape es] at h
    simpa only [R, eval_prod, eval_shiftPolynomial] using h
  refine ⟨R, ?_, hR⟩
  obtain ⟨b, hb⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks (expand ds) (expand es))
  intro hz
  have hs : b < ((b + 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
  apply hb _ hs
  change L[expand ds, expand es].denominator _ = 0
  rw [hR, hz, eval_zero, zero_mul]

private theorem exists_polynomial_of_mul_eval {F : ℂ → ℂ} (hF : Continuous F)
    (P R : Polynomial ℂ) (hR : R ≠ 0) (h : ∀ s, P.eval s = R.eval s * F s) :
    ∃ Q : Polynomial ℂ, F = Q.eval := by
  suffices h' : ∀ (n : ℕ) (R P : Polynomial ℂ), R.natDegree = n → R ≠ 0 →
      (∀ s, P.eval s = R.eval s * F s) → ∃ Q : Polynomial ℂ, F = Q.eval from
    h' R.natDegree R P rfl hR h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R P hDeg hR hEval
    by_cases hRpos : 0 < R.natDegree
    · obtain ⟨x, hx⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hRpos)
      have hx' : P.IsRoot x := by
        change P.eval x = 0
        rw [hEval x, show R.eval x = 0 from hx, zero_mul]
      obtain ⟨R', hR'⟩ := dvd_iff_isRoot.mpr hx
      obtain ⟨P', hP'⟩ := dvd_iff_isRoot.mpr hx'
      have hRne : R' ≠ 0 := by intro hz; exact hR (by rw [hR', hz, mul_zero])
      have hlt : R'.natDegree < n := by
        rw [hR', natDegree_mul (X_sub_C_ne_zero x) hRne, natDegree_X_sub_C] at hDeg
        omega
      have heq : P'.eval = fun z => R'.eval z * F z := by
        apply (dense_compl_singleton x).denseRange_val.equalizer P'.continuous (R'.continuous.mul hF)
        funext z
        have hz : (z : ℂ) ≠ x := z.property
        have he := hEval z.val
        rw [hP', hR', eval_mul, eval_mul, eval_sub, eval_X, eval_C, mul_assoc] at he
        exact mul_left_cancel₀ (sub_ne_zero.mpr hz) he
      exact ih R'.natDegree hlt R' P' rfl hRne (congrFun heq)
    · have hconst := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hRpos)
      have hcoeff : R.coeff 0 ≠ 0 := fun hz => hR (hconst.trans (by rw [hz, C_0]))
      refine ⟨C (R.coeff 0)⁻¹ * P, funext fun s => ?_⟩
      have he := hEval s
      conv at he => rhs; rw [hconst, eval_C]
      rw [eval_mul, eval_C, he, ← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul]

/-- If the two pair denominators differ by a nonzero polynomial factor, a polynomial
normalization for the larger denominator gives polynomiality for an entire normalization
by the smaller denominator. -/
theorem OrdinaryIntegralNormalization.polynomial_of_denominator_mul {I : ℂ → ℂ}
    {F G : ReciprocalEntire} (R P : Polynomial ℂ) (hR : R ≠ 0)
    (hDen : ∀ s, F.denominator s = R.eval s * G.denominator s)
    (hF : ∃ b : ℝ, ∀ s : ℂ, b < s.re → F.denominator s ≠ 0)
    (M : OrdinaryIntegralNormalization I (fun s => (F.denominator s)⁻¹))
    (N : OrdinaryIntegralNormalization I (fun s => (G.denominator s)⁻¹)) (hP : M.value = P.eval) :
    ∃ Q : Polynomial ℂ, N.value = Q.eval := by
  obtain ⟨b, hb⟩ := hF
  obtain ⟨c, hc⟩ := N.eq_on_right
  have hN : Differentiable ℂ N.value := fun s => (N.analytic s (mem_univ s)).differentiableAt
  let T : OrdinaryIntegralNormalization I (fun s => (F.denominator s)⁻¹) :=
    ⟨fun s => R.eval s * N.value s, fun s h => (R.differentiable.analyticAt s).mul (N.analytic s h), max b c,
      fun s hs => by
        have hr : R.eval s ≠ 0 := fun hz => hb s ((le_max_left _ _).trans_lt hs) (by rw [hDen, hz, zero_mul])
        rw [hc s ((le_max_right _ _).trans_lt hs), hDen, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hr, one_mul]⟩
  have he := M.value_eq_of_factor_ne_zero T ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩
  rw [hP] at he
  exact exists_polynomial_of_mul_eval hN.continuous P R hR (congrFun he)

/-- Every test in a family admits an entire normalization given by a polynomial. -/
def HasPolynomialOrdinaryNormalizations {Test : Type*} (I : Test → ℂ → ℂ) (L : ReciprocalEntire) : Prop :=
  ∀ i, ∃ (N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹))
    (P : Polynomial ℂ), N.value = P.eval

/-- Polynomiality at the two standard real additive scales for equal ranks with a
standard polynomial Gaussian row, and for all adjacent-rank tests. -/
def RealOrdinaryPolynomialStatement (l : List RealBlock → Prop) : Prop :=
  (∀ (r : ℕ) (ds es : List RealBlock), l ds → l es → realRank ds = r + 2 → realRank es = r + 1 →
    ∀ (a : ℝˣ), (a = 1 ∨ a = -1) → ∀ D : RealQuotientMeasureData r,
      HasPolynomialOrdinaryNormalizations (realOrdinaryUnequalTest (r := r + 1) (t := r) (Nat.lt_succ_self r) ds es a D) L[ds, es]) ∧
  ∀ (r : ℕ) (ds es : List RealBlock), l ds → l es → realRank ds = r + 1 → realRank es = r + 1 →
    ∀ (a : ℝˣ), (a = 1 ∨ a = -1) → ∀ D : RealQuotientMeasureData r,
      HasPolynomialOrdinaryNormalizations (gaussianEqualIntegral r ds es a Real.pi D) L[ds, es]

private theorem exactModel_le_ascending {r : ℕ} (ds : List RealBlock) (hd : realRank ds = r + 1) (a : ℝˣ) :
    realWhittakerModel r ds a ≤ realWhittakerModel r (ascendingExpand ds) a := by
  rw [realWhittakerModels_eq r ds hd a, realWhittakerModels_eq r (ascendingExpand ds)
    ((realRank_ascendingExpand ds).trans hd) a]
  exact uniformModel_le_ascendingExpand r ds hd a

private theorem polynomial_of_ascending {I : ℂ → ℂ} (ds es : List RealBlock)
    (M : OrdinaryIntegralNormalization I (fun s => (L[ascendingExpand ds, ascendingExpand es].denominator s)⁻¹))
    (N : OrdinaryIntegralNormalization I (fun s => (L[ds, es].denominator s)⁻¹))
    (P : Polynomial ℂ) (hP : M.value = P.eval) : ∃ Q : Polynomial ℂ, N.value = Q.eval := by
  obtain ⟨R, hR, hDen⟩ := exists_expandPairDenominatorPolynomial ds es
  have hL := realPairLFactor_perm (ascendingExpand_perm ds) (ascendingExpand_perm es)
  refine M.polynomial_of_denominator_mul R P hR (fun s => ?_) ?_ N hP
  · rw [hL, hDen]
  · exact ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks (ascendingExpand ds) (ascendingExpand es))

/-- Exact entire continuation and polynomiality for the character lists imply polynomiality
for the original real block lists. -/
def RealOrdinaryPolynomialReductionStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement → RealOrdinaryPolynomialStatement IsRealCharacterList →
    RealOrdinaryPolynomialStatement (fun _ => True)

private theorem hasPolynomial_of_ascending {X Y : Type*} (ds es : List RealBlock)
    {I : X → ℂ → ℂ} {J : Y → ℂ → ℂ} (f : X → Y) (hf : ∀ x, J (f x) = I x)
    (hO : HasEntireOrdinaryNormalizations I L[ds, es])
    (hPoly : HasPolynomialOrdinaryNormalizations J L[ascendingExpand ds, ascendingExpand es]) :
    HasPolynomialOrdinaryNormalizations I L[ds, es] := by
  intro x
  obtain ⟨M, P, hP⟩ := hPoly (f x)
  obtain ⟨N⟩ := hO x
  let M' : OrdinaryIntegralNormalization (I x)
      (fun s => (L[ascendingExpand ds, ascendingExpand es].denominator s)⁻¹) :=
    ⟨M.value, M.analytic, hf x ▸ M.eq_on_right⟩
  obtain ⟨Q, hQ⟩ := polynomial_of_ascending ds es M' N P hP
  exact ⟨N, Q, hQ⟩

private theorem unequalCharacterTests_constructor
    (hPoly : RealOrdinaryPolynomialStatement IsRealCharacterList)
    (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 2) (he : realRank es = r + 1)
    (a : ℝˣ) (ha : a = 1 ∨ a = -1) (D : RealQuotientMeasureData r) :
    HasPolynomialOrdinaryNormalizations
      (realOrdinaryUnequalTest (r := r + 1) (t := r) (Nat.lt_succ_self r) (ascendingExpand ds) (ascendingExpand es) a D)
      L[ascendingExpand ds, ascendingExpand es] :=
  hPoly.1 r (ascendingExpand ds) (ascendingExpand es) ⟨ascendingCharacters ds, rfl⟩ ⟨ascendingCharacters es, rfl⟩
    ((realRank_ascendingExpand ds).trans hd) ((realRank_ascendingExpand es).trans he) a ha D

private theorem unequalAscendingTest_eq (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 2)
    (he : realRank es = r + 1) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (x : realWhittakerModel (r + 1) ds a × realWhittakerModel r es (-a)) :
    realOrdinaryUnequalTest (r := r + 1) (t := r) (Nat.lt_succ_self r) (ascendingExpand ds) (ascendingExpand es) a D
      (Prod.map (Submodule.inclusion (exactModel_le_ascending ds hd a))
        (Submodule.inclusion (exactModel_le_ascending es he (-a))) x) =
      realOrdinaryUnequalTest (r := r + 1) (t := r) (Nat.lt_succ_self r) ds es a D x := by
  unfold realOrdinaryUnequalTest
  rw [Prod.map_fst, Prod.map_snd, Submodule.coe_inclusion, Submodule.coe_inclusion]

private theorem realAdjacentPolynomial_of_characterTests
    (hO : RealOrdinaryNormalizedContinuationStatement) (hPoly : RealOrdinaryPolynomialStatement IsRealCharacterList)
    (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 2) (he : realRank es = r + 1)
    (a : ℝˣ) (ha : a = 1 ∨ a = -1) (D : RealQuotientMeasureData r) :
    HasPolynomialOrdinaryNormalizations (realOrdinaryUnequalTest (r := r + 1) (Nat.lt_succ_self r) ds es a D) L[ds, es] :=
  hasPolynomial_of_ascending ds es _ (unequalAscendingTest_eq r ds es hd he a D)
    (hO.1 (r + 1) r (Nat.lt_succ_self r) ds es hd he a D)
    (unequalCharacterTests_constructor hPoly r ds es hd he a ha D)

private def ascendingGaussianTest (r : ℕ) (ds es : List RealBlock)
    (hd : realRank ds = r + 1) (he : realRank es = r + 1) (a : ℝˣ)
    (i : GaussianEqualTest r ds es a Real.pi) : GaussianEqualTest r (ascendingExpand ds) (ascendingExpand es) a Real.pi :=
  Prod.map (Submodule.inclusion (exactModel_le_ascending ds hd a))
    (Prod.map (Submodule.inclusion (exactModel_le_ascending es he (-a))) id) i

private theorem gaussianEqualIntegral_eq (r : ℕ) (ds es : List RealBlock) (a : ℝˣ)
    (D : RealQuotientMeasureData r) (i : GaussianEqualTest r ds es a Real.pi) :
    gaussianEqualIntegral r ds es a Real.pi D i = realEqualIntegral D i.1.val i.2.1.val i.2.2.val := rfl

private theorem ascendingGaussianTest_row (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 1)
    (he : realRank es = r + 1) (a : ℝˣ) (i : GaussianEqualTest r ds es a Real.pi) :
    (ascendingGaussianTest r ds es hd he a i).2.2 = i.2.2 := by
  unfold ascendingGaussianTest
  rw [Prod.map_snd, Prod.map_snd]
  rfl

private theorem equalAscendingTest_eq (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 1)
    (he : realRank es = r + 1) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (i : GaussianEqualTest r ds es a Real.pi) :
    gaussianEqualIntegral r (ascendingExpand ds) (ascendingExpand es) a Real.pi D (ascendingGaussianTest r ds es hd he a i) =
      gaussianEqualIntegral r ds es a Real.pi D i := by
  let j := ascendingGaussianTest r ds es hd he a i
  have hW : j.1.val = i.1.val := by
    unfold j ascendingGaussianTest
    rw [Prod.map_fst, Submodule.coe_inclusion]
  have hV : j.2.1.val = i.2.1.val := by
    unfold j ascendingGaussianTest
    rw [Prod.map_snd, Prod.map_fst, Submodule.coe_inclusion]
  have hRow : j.2.2.val = i.2.2.val := congrArg Subtype.val (ascendingGaussianTest_row r ds es hd he a i)
  let Z (f : (Langlands.GeneralLinear (r + 1) ℝ → ℂ) × (Langlands.GeneralLinear (r + 1) ℝ → ℂ) ×
      𝓢(Fin (r + 1) → ℝ, ℂ)) := realEqualIntegral D f.1 f.2.1 f.2.2
  have hData : (j.1.val, j.2.1.val, j.2.2.val) = (i.1.val, i.2.1.val, i.2.2.val) :=
    Prod.ext hW (Prod.ext hV hRow)
  have hI := congrArg Z hData
  exact (gaussianEqualIntegral_eq r (ascendingExpand ds) (ascendingExpand es) a D j).trans
    (hI.trans (gaussianEqualIntegral_eq r ds es a D i).symm)

private theorem gaussianEntire_of_ordinary (hO : RealOrdinaryNormalizedContinuationStatement)
    (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 1) (he : realRank es = r + 1)
    (a : ℝˣ) (D : RealQuotientMeasureData r) :
    HasEntireOrdinaryNormalizations (gaussianEqualIntegral r ds es a Real.pi D) L[ds, es] :=
  fun i => hO.2 r ds es hd he a D (i.1, i.2.1, i.2.2.val)

private theorem equalCharacterTests_constructor
    (hPoly : RealOrdinaryPolynomialStatement IsRealCharacterList)
    (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 1) (he : realRank es = r + 1)
    (a : ℝˣ) (ha : a = 1 ∨ a = -1) (D : RealQuotientMeasureData r) :
    HasPolynomialOrdinaryNormalizations (gaussianEqualIntegral r (ascendingExpand ds) (ascendingExpand es) a Real.pi D)
      L[ascendingExpand ds, ascendingExpand es] :=
  hPoly.2 r (ascendingExpand ds) (ascendingExpand es) ⟨ascendingCharacters ds, rfl⟩ ⟨ascendingCharacters es, rfl⟩
    ((realRank_ascendingExpand ds).trans hd) ((realRank_ascendingExpand es).trans he) a ha D

private theorem realEqualPolynomial_of_characterTests
    (hO : RealOrdinaryNormalizedContinuationStatement) (hPoly : RealOrdinaryPolynomialStatement IsRealCharacterList)
    (r : ℕ) (ds es : List RealBlock) (hd : realRank ds = r + 1) (he : realRank es = r + 1)
    (a : ℝˣ) (ha : a = 1 ∨ a = -1) (D : RealQuotientMeasureData r) :
    HasPolynomialOrdinaryNormalizations (gaussianEqualIntegral r ds es a Real.pi D) L[ds, es] :=
  hasPolynomial_of_ascending ds es _ (equalAscendingTest_eq r ds es hd he a D)
    (gaussianEntire_of_ordinary hO r ds es hd he a D)
    (equalCharacterTests_constructor hPoly r ds es hd he a ha D)

theorem realOrdinaryPolynomialReduction : RealOrdinaryPolynomialReductionStatement :=
  fun hO hPoly => ⟨fun r ds es _ _ => realAdjacentPolynomial_of_characterTests hO hPoly r ds es,
    fun r ds es _ _ => realEqualPolynomial_of_characterTests hO hPoly r ds es⟩

end Langlands.Global.RankinSelbergGlobal
