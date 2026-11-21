import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.RankinSelberg.PadicGenericGammaExpression
import Langlands.Representation.RankinSelberg.PoleOrderAtZeroArithmetic
import Langlands.Representation.RankinSelberg.SelfPairSupercuspidality
import Langlands.Representation.RankinSelberg.UnitaryGenericLPolynomialNonvanishingProof
import Langlands.Representation.Unitary.Restriction

/-! # Spectral orders from the Rankin–Selberg denominator polynomials -/

noncomputable section

set_option autoImplicit false

namespace Langlands.RankinSelberg

open Polynomial LocalFactor

private theorem meromorphicOrderAt_polynomial_eval (P : ℂ[X]) (hP : P ≠ 0) (z : ℂ) :
    meromorphicOrderAt (fun x => P.eval x) z = (P.rootMultiplicity z : ℤ) := by
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP z
  have ha : AnalyticAt ℂ (fun x => Q.eval x) z := by
    simpa [aeval_def] using (analyticAt_id (z := z)).aeval_polynomial Q
  have hzero : meromorphicOrderAt (fun x => Q.eval x) z = 0 := by
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr]
    · rfl
    · exact fun hx => hQ (dvd_iff_isRoot.mpr hx)
  have hfun : (fun x => P.eval x) =
      ((· - z) ^ P.rootMultiplicity z) * (fun x => Q.eval x) := by
    funext x
    change P.eval x = (x - z) ^ P.rootMultiplicity z * Q.eval x
    simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] using
      congrArg (fun p : ℂ[X] => p.eval x) hPQ
  rw [hfun, meromorphicOrderAt_mul (by fun_prop) ha.meromorphicAt,
    meromorphicOrderAt_pow_id_sub_const, hzero, add_zero]
  exact (WithTop.coe_natCast _).symm

private theorem deriv_spectralPoint_ne_zero (q : ℕ) (hq : 1 < q) (z : ℂ) :
    deriv (spectralPoint q) z ≠ 0 := by
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans hq1
  have hfun : spectralPoint q = fun s => Complex.exp (-s * (Real.log (q : ℝ) : ℂ)) :=
    funext fun s => spectralPoint_eq_spectralParameter q hq0 s
  have hd : HasDerivAt (fun s : ℂ => Complex.exp (-s * (Real.log (q : ℝ) : ℂ)))
      (Complex.exp (-z * (Real.log (q : ℝ) : ℂ)) * (-1 * (Real.log (q : ℝ) : ℂ))) z :=
    ((hasDerivAt_id z).neg.mul_const (Real.log (q : ℝ) : ℂ)).cexp
  rw [hfun, hd.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (neg_ne_zero.mpr one_ne_zero)
    (Complex.ofReal_ne_zero.mpr (Real.log_pos hq1).ne'))

/-- Evaluation at the spectral parameter preserves the exact polynomial root
multiplicity because the exponential has nonzero derivative. -/
theorem meromorphicOrderAt_eval_spectralPoint
    (q : ℕ) (hq : 1 < q) (P : ℂ[X]) (hP : P ≠ 0) (z : ℂ) :
    meromorphicOrderAt (fun x => P.eval (spectralPoint q x)) z =
      (P.rootMultiplicity (spectralPoint q z) : ℤ) := by
  have ha : AnalyticAt ℂ (spectralPoint q) z := by
    simpa only [eval_X] using analyticAt_polynomial_spectralPoint q hq X z
  exact (meromorphicOrderAt_comp_of_deriv_ne_zero (f := fun x => P.eval x)
    ha (deriv_spectralPoint_ne_zero q hq z)).trans
    (meromorphicOrderAt_polynomial_eval P hP (spectralPoint q z))

/-- The order of the rational gamma at a spectral point is the forward root
multiplicity minus the reflected root multiplicity. -/
theorem meromorphicOrderAt_rationalGammaExpression
    (q : ℕ) (hq : 1 < q) (δ c : ℂˣ) (hδ : (δ : ℂ) = (q : ℂ)⁻¹) (m : ℤ)
    (P Pd : ℂ[X]) (hP : P ≠ 0) (hPd : Pd ≠ 0) (z : ℂ) :
    meromorphicOrderAt (rationalSpectralValue q (rationalGammaExpression δ c m P Pd)) z =
      ((P.rootMultiplicity (spectralPoint q z) : ℤ) -
        (Pd.rootMultiplicity (spectralPoint q (1 - z)) : ℤ) : ℤ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hε := epsilonMonomial_analyticAt q hq0 c m z
  have hε0 : meromorphicOrderAt (epsilonMonomial q c m) z = 0 := by
    rw [hε.meromorphicOrderAt_eq,
      hε.analyticOrderAt_eq_zero.mpr (epsilonMonomial_ne_zero q hq0 c m z)]
    rfl
  have ha := analyticAt_polynomial_spectralPoint q hq P z
  have had : AnalyticAt ℂ (fun x => Pd.eval (spectralPoint q (1 - x))) z :=
    (analyticAt_polynomial_spectralPoint q hq Pd (1 - z)).comp
      (analyticAt_const.sub analyticAt_id)
  have hd : deriv (fun x : ℂ => 1 - x) z ≠ 0 := by
    have h : HasDerivAt (fun x : ℂ => 1 - x) (0 - 1) z :=
      (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)
    rw [h.deriv]
    norm_num
  have hr : meromorphicOrderAt (fun x => Pd.eval (spectralPoint q (1 - x))) z =
      (Pd.rootMultiplicity (spectralPoint q (1 - z)) : ℤ) :=
    (meromorphicOrderAt_comp_of_deriv_ne_zero (f := fun x => Pd.eval (spectralPoint q x))
      (analyticAt_const.sub analyticAt_id) hd).trans
      (meromorphicOrderAt_eval_spectralPoint q hq Pd hPd (1 - z))
  rw [meromorphicOrderAt_congr
    (rationalSpectralValue_eventuallyEq_polynomialGammaExpression q hq δ c hδ m P Pd hPd z)]
  change meromorphicOrderAt (epsilonMonomial q c m * (fun x => Pd.eval (spectralPoint q (1 - x)))⁻¹ /
    (fun x => P.eval (spectralPoint q x))⁻¹) z = _
  rw [meromorphicOrderAt_div (hε.meromorphicAt.mul had.meromorphicAt.inv) ha.meromorphicAt.inv,
    meromorphicOrderAt_mul hε.meromorphicAt had.meromorphicAt.inv]
  simp only [meromorphicOrderAt_inv,
    hε0, zero_add, meromorphicOrderAt_eval_spectralPoint q hq P hP z, hr]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg,
    ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_inj]
  omega

section SelfPair

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV

/-- For a generic unitarizable action, the self-pair gamma orders alone
suffice for the local supercuspidality criterion. -/
def SupercuspidalOfSelfPairGammaOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (r : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier)),
      IsGeneric ψ r π.representation → IsUnitarizable π.representation →
      ∀ (G : RatFunc ℂ),
        IsPadicSymmetricGammaFactor F ψ ν.val
          π.representation (smoothContragredient π.representation) G →
        (∀ t : ℝ, 0 < meromorphicOrderAt
          (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
          t = 0) →
        meromorphicOrderAt
          (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) 0 = 1 →
        GeneralLinear.IsSupercuspidal π.representation

set_option maxHeartbeats 800000 in
theorem supercuspidalOfSelfPairGammaOrder : SupercuspidalOfSelfPairGammaOrderStatement.{uF, uV} := by
  intro p _ F ψ ν r
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (r + 1)
  intro π hπ hU G hG hzero hord
  let ρ := π.representation
  let ρd := smoothContragredient ρ
  have hπd : IsGeneric ψ r ρd := isGeneric_contragredient hπ
  let P := genericSymmetricLPolynomial F ψ ν.val ρ ρd hπ hπd
  let Pd := genericSymmetricDualLPolynomial F ψ ν.val ρ ρd hπ hπd
  let ε := genericSymmetricEpsilonData F ψ ν.val ν.property ρ ρd hπ hπd
  have hP : IsPadicSymmetricLPolynomial F ψ ν.val ρ ρd P :=
    genericSymmetricLPolynomial_isPadic F ψ ν.val ρ ρd hπ hπd
  have hPd : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback ρ) (inverseTransposePullback ρd) Pd :=
    genericSymmetricDualLPolynomial_isPadic F ψ ν.val ρ ρd hπ hπd
  have he : G = rationalGammaExpression (residueReflection F) ε.1 ε.2 P Pd :=
    (genericSymmetricGammaFactor_eq F ψ ν.val ν.property ρ ρd hπ hπd hG).symm.trans
      (genericSymmetricGammaFactor_eq_expression F ψ ν.val ν.property ρ ρd hπ hπd)
  have hUd : IsUnitarizable ρd := by
    obtain ⟨b⟩ := hU
    let e := b.smoothDualEquiv (compactOpen_cofinal F T (r + 1)) hπ.2.1
    exact (isUnitarizable_iff_of_conjugateEquiv
      (ρ := ρ) (σ := ρd) e (b.toSmoothDual_apply_action hπ.2.1.1)).mp ⟨b⟩
  have hPd1 : Pd.eval (spectralPoint T.residueCardinality 1) ≠ 0 :=
    UnitaryGeneric.unitaryGenericLPolynomialNonvanishing p F (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν) r r
      (inverseTransposePullback ρ) (inverseTransposePullback ρd)
      (HighlyRamified.isGeneric_inverseTransposePullback F ψ ρ hπ)
      (hU.comp _) (HighlyRamified.isGeneric_inverseTransposePullback F ψ ρd hπd)
      (hUd.comp _) Pd hPd 1 (by simp)
  have hPdRoot : Pd.rootMultiplicity (spectralPoint T.residueCardinality 1) = 0 :=
    rootMultiplicity_eq_zero hPd1
  rw [he, meromorphicOrderAt_rationalGammaExpression T.residueCardinality
    T.residueCardinality_gt_one _ _ (coe_residueReflection F) _ P Pd
    (ne_zero_of_coeff_zero_eq_one hP.coeff_zero) (ne_zero_of_coeff_zero_eq_one hPd.coeff_zero),
    sub_zero, hPdRoot, Nat.cast_zero, sub_zero] at hord
  have hpoint : spectralPoint T.residueCardinality 0 = 1 := by simp [spectralPoint]
  rw [hpoint] at hord
  have hP0 : lPolynomialPoleOrderAtZero P = 1 := by exact_mod_cast hord
  exact supercuspidalOfSelfPair p F ψ ν r π hπ hU G P hG hP hzero hP0

end SelfPair

end Langlands.RankinSelberg
