import Langlands.LocalFactor.Archimedean.Definitions
import Mathlib.Topology.Algebra.Polynomial

/-! # Finite conductor exponents in the presence of archimedean Gamma factors -/

noncomputable section

open Filter Polynomial Topology
open scoped Topology

namespace Langlands.LocalFactor.Archimedean

/-- The shifts of the real Gamma factors obtained by expanding one block, using
`Γ_ℂ(z) = Γ_ℝ(z) Γ_ℝ(z + 1)`. -/
def GammaBlock.realShifts : GammaBlock → List ℂ
  | .real a => [a]
  | .complex a => [a, a + 1]

private def realGammaValue (shifts : List ℂ) (z : ℂ) : ℂ :=
  (shifts.map fun a => Complex.Gammaℝ (z + a)).prod

private theorem gammaProduct_value_realShifts (blocks : List GammaBlock) (z : ℂ) :
    ((gammaProduct blocks).denominator z)⁻¹ = realGammaValue (blocks.flatMap GammaBlock.realShifts) z := by
  induction blocks with
  | nil => simp [gammaProduct, ReciprocalEntire.product, ReciprocalEntire.one, realGammaValue]
  | cons b bs ih =>
    change ((b.factor.mul (gammaProduct bs)).denominator z)⁻¹ = _
    rw [ReciprocalEntire.denominator_mul, mul_inv, ih]
    simp only [List.flatMap_cons, realGammaValue, List.map_append, List.prod_append]
    congr 1
    cases b with
    | real a => simp [GammaBlock.factor, GammaBlock.realShifts, gammaReal,
        ReciprocalEntire.denominator_shift]
    | complex a =>
      simp only [GammaBlock.factor, GammaBlock.realShifts, gammaComplex,
        ReciprocalEntire.denominator_shift, inv_inv, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, ← add_assoc, Complex.Gammaℝ_mul_Gammaℝ_add_one]

private theorem realGammaValue_eventually_ne_zero (shifts : List ℂ) :
    ∀ᶠ z in codiscrete ℂ, realGammaValue shifts z ≠ 0 := by
  have hs : (shifts.map GammaBlock.real).flatMap GammaBlock.realShifts = shifts := by
    induction shifts with
    | nil => rfl
    | cons a shifts ih => simpa [GammaBlock.realShifts] using congrArg (List.cons a) ih
  have h := eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
    (gammaProduct (shifts.map GammaBlock.real)).denominator_eventually_ne_zero
  filter_upwards [h] with z hz
  have he := gammaProduct_value_realShifts (shifts.map GammaBlock.real) z
  rw [hs] at he
  exact he ▸ inv_ne_zero hz

private theorem eventually_codiscrete_comp {g : ℂ → ℂ} (hg : Continuous g)
    (hinj : Function.Injective g) {P : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, P z) :
    ∀ᶠ z in codiscrete ℂ, P (g z) := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE] at h ⊢
  intro x
  have ht : Tendsto g (𝓝[≠] x) (𝓝[≠] g x) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    exact eventually_of_mem self_mem_nhdsWithin fun y hy hgy => hy (hinj hgy)
  exact ht.eventually (h (g x))

private theorem two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

private def gammaShiftPolynomial (shifts : List ℂ) (slope offset : ℂ) : ℂ[X] :=
  (shifts.map fun a => C (slope / (2 * (Real.pi : ℂ))) * (X + C ((offset + a) / slope))).prod

private theorem gammaShiftPolynomial_leadingCoeff (shifts : List ℂ) (slope offset : ℂ) :
    (gammaShiftPolynomial shifts slope offset).leadingCoeff =
      (slope / (2 * (Real.pi : ℂ))) ^ shifts.length := by
  induction shifts with
  | nil => simp [gammaShiftPolynomial]
  | cons a shifts ih =>
    simp only [gammaShiftPolynomial, List.map_cons, List.prod_cons, List.length_cons,
      leadingCoeff_mul, (monic_X_add_C _).leadingCoeff_C_mul, pow_succ'] at ih ⊢
    rw [ih]

private theorem gammaShiftPolynomial_eval (shifts : List ℂ) {slope offset z : ℂ}
    (hslope : slope ≠ 0) : (gammaShiftPolynomial shifts slope offset).eval z =
    (shifts.map fun a => (slope * z + offset + a) / (2 * (Real.pi : ℂ))).prod := by
  induction shifts with
  | nil => simp [gammaShiftPolynomial]
  | cons a shifts ih =>
    simp only [gammaShiftPolynomial, List.map_cons, List.prod_cons, eval_mul, eval_add,
      eval_C, eval_X] at ih ⊢
    rw [ih]
    congr 1
    field_simp
    ring

private theorem realGammaValue_add_two (shifts : List ℂ) {slope offset z : ℂ} (hslope : slope ≠ 0)
    (h : realGammaValue shifts (slope * z + offset) ≠ 0) :
    realGammaValue shifts (slope * z + offset + 2) = realGammaValue shifts (slope * z + offset) *
      (gammaShiftPolynomial shifts slope offset).eval z := by
  rw [gammaShiftPolynomial_eval shifts hslope]
  induction shifts with
  | nil => simp [realGammaValue]
  | cons a shifts ih =>
    simp only [realGammaValue, List.map_cons, List.prod_cons] at h ih ⊢
    obtain ⟨ha, hs⟩ := mul_ne_zero_iff.mp h
    have ha₀ : slope * z + offset + a ≠ 0 := by
      intro he
      exact ha (Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simpa using he⟩)
    rw [ih hs, (by ring : slope * z + offset + 2 + a = (slope * z + offset + a) + 2),
      Complex.Gammaℝ_add_two ha₀, div_div]
    ring

private theorem base_eq_one_of_realGammaRatio
    (A B Ad Bd : List ℂ) (hAB : A.length = B.length) (hAdBd : Ad.length = Bd.length)
    (M : ℝ) (hM : 0 < M) (c : ℂˣ)
    (h : ∀ᶠ z in codiscrete ℂ,
      realGammaValue A z * realGammaValue Bd (1 - z) =
        (c : ℂ) * (M : ℂ) ^ (-z) * (realGammaValue B z * realGammaValue Ad (1 - z))) : M = 1 := by
  let PA := gammaShiftPolynomial A 1 0
  let PB := gammaShiftPolynomial B 1 0
  let PAd := gammaShiftPolynomial Ad (-1) (-1)
  let PBd := gammaShiftPolynomial Bd (-1) (-1)
  let baseShift : ℂ := (M : ℂ) ^ (-(2 : ℂ))
  have hM₀ : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  have h2 := eventually_codiscrete_comp (g := fun z => z + 2) (by fun_prop)
    (fun _ _ he => add_right_cancel he) h
  have hback (C : List ℂ) : ∀ᶠ z : ℂ in codiscrete ℂ, realGammaValue C ((-1) * z + (-1)) ≠ 0 :=
    eventually_codiscrete_comp (by fun_prop) (fun x y he => by linear_combination -he)
      (realGammaValue_eventually_ne_zero C)
  have heval : ∀ᶠ z in codiscrete ℂ, (PA * PAd).eval z = (C baseShift * (PB * PBd)).eval z := by
    filter_upwards [h, h2, realGammaValue_eventually_ne_zero A,
      realGammaValue_eventually_ne_zero B, hback Ad, hback Bd] with z hz hz2 hA hB hAd hBd
    have ha := realGammaValue_add_two A (slope := 1) (offset := 0) (z := z) one_ne_zero
      (by simpa using hA)
    have hb := realGammaValue_add_two B (slope := 1) (offset := 0) (z := z) one_ne_zero
      (by simpa using hB)
    have had := realGammaValue_add_two Ad (neg_ne_zero.mpr one_ne_zero) hAd
    have hbd := realGammaValue_add_two Bd (neg_ne_zero.mpr one_ne_zero) hBd
    simp only [one_mul, add_zero] at ha hb
    rw [(by ring : (-1 : ℂ) * z + (-1) + 2 = 1 - z)] at had hbd
    change realGammaValue A (z + 2) = realGammaValue A z * PA.eval z at ha
    change realGammaValue B (z + 2) = realGammaValue B z * PB.eval z at hb
    change realGammaValue Ad (1 - z) = realGammaValue Ad ((-1) * z + (-1)) * PAd.eval z at had
    change realGammaValue Bd (1 - z) = realGammaValue Bd ((-1) * z + (-1)) * PBd.eval z at hbd
    rw [had, hbd] at hz
    change realGammaValue A (z + 2) * realGammaValue Bd (1 - (z + 2)) =
      (c : ℂ) * (M : ℂ) ^ (-(z + 2)) *
        (realGammaValue B (z + 2) * realGammaValue Ad (1 - (z + 2))) at hz2
    rw [ha, hb, (by ring : (1 : ℂ) - (z + 2) = (-1) * z + (-1)), neg_add,
      Complex.cpow_add _ _ hM₀] at hz2
    change (realGammaValue A z * PA.eval z) * realGammaValue Bd ((-1) * z + (-1)) =
      (c : ℂ) * ((M : ℂ) ^ (-z) * baseShift) *
        ((realGammaValue B z * PB.eval z) * realGammaValue Ad ((-1) * z + (-1))) at hz2
    simp only [eval_mul, eval_C]
    have hcancel : (c : ℂ) * (M : ℂ) ^ (-z) *
        (realGammaValue B z * realGammaValue Ad ((-1) * z + (-1))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero c.ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hM₀)))
        (mul_ne_zero hB hAd)
    apply mul_left_cancel₀ hcancel
    linear_combination hz2 * PBd.eval z - hz * PA.eval z
  have hpoly : PA * PAd = C baseShift * (PB * PBd) := by
    by_contra hneq
    have hn := eventually_eval_ne_zero_codiscrete (sub_ne_zero.mpr hneq)
    obtain ⟨z, he, hnz⟩ := ((heval.and hn).filter_mono (nhdsNE_le_codiscrete (0 : ℂ))).exists
    exact hnz (by rw [eval_sub, he, sub_self])
  have hl := congrArg Polynomial.leadingCoeff hpoly
  simp only [leadingCoeff_mul, leadingCoeff_C, PA, PB, PAd, PBd, gammaShiftPolynomial_leadingCoeff,
    hAB, hAdBd] at hl
  have hfactor : ((1 : ℂ) / (2 * (Real.pi : ℂ))) ^ B.length *
      ((-1 : ℂ) / (2 * (Real.pi : ℂ))) ^ Bd.length ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (div_ne_zero one_ne_zero two_pi_ne_zero))
      (pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr one_ne_zero) two_pi_ne_zero))
  have hbase : (1 : ℂ) = baseShift := by
    apply mul_right_cancel₀ hfactor
    simpa only [one_mul] using hl
  have hm : (M : ℂ) ^ (2 : ℕ) = 1 := by
    rw [← Complex.cpow_natCast]
    simpa [baseShift, Complex.cpow_neg] using hbase.symm
  have hmR : M ^ 2 = 1 := by exact_mod_cast hm
  nlinarith

/-- If the real-Gamma counts agree in two archimedean products and in their two
reflected products, the quotient of the resulting ratios cannot carry a nontrivial
positive exponential base. Values agree away from a closed discrete set. -/
def ArchimedeanGammaExponentComparisonStatement : Prop :=
  ∀ (A B Ad Bd : List GammaBlock),
    (A.flatMap GammaBlock.realShifts).length = (B.flatMap GammaBlock.realShifts).length →
    (Ad.flatMap GammaBlock.realShifts).length = (Bd.flatMap GammaBlock.realShifts).length →
    ∀ (M : ℝ), 0 < M → ∀ (c : ℂˣ),
      (∀ᶠ z in codiscrete ℂ,
        ((gammaProduct A).denominator z)⁻¹ * ((gammaProduct Bd).denominator (1 - z))⁻¹ =
          (c : ℂ) * (M : ℂ) ^ (-z) *
            (((gammaProduct B).denominator z)⁻¹ * ((gammaProduct Ad).denominator (1 - z))⁻¹)) →
      M = 1

theorem archimedeanGammaExponentComparison : ArchimedeanGammaExponentComparisonStatement := by
  intro A B Ad Bd hAB hAdBd M hM c h
  apply base_eq_one_of_realGammaRatio _ _ _ _ hAB hAdBd M hM c
  simpa only [gammaProduct_value_realShifts] using h

end Langlands.LocalFactor.Archimedean
