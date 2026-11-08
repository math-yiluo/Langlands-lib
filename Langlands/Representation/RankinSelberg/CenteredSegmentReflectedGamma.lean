import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.Representation.RankinSelberg.CenteredSegmentFamilyGamma
import Langlands.Representation.RankinSelberg.SmoothDualPairFactors

/-! # Centered gamma germs from a reflected ratio -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker Polynomial Classification LocalFactor

universe uF uV uW uX uI

/-- A rational function has the displayed polynomial ratio up to an actual
nonzero epsilon monomial. -/
def HasRationalGammaExpression (δ : ℂˣ) (P Pd : ℂ[X]) (G : RatFunc ℂ) : Prop :=
  ∃ (c : ℂˣ) (m : ℤ), G = rationalGammaExpression δ c m P Pd

/-- A Laurent-monomial discrepancy between the two reflected ratios is
absorbed by the epsilon coefficient and exponent. -/
theorem TemperedLFactorGamma.ReflectedRatioData.gammaExpression_eq
    {δ : ℂˣ} {P Pd B Bd : ℂ[X]}
    (r : TemperedLFactorGamma.ReflectedRatioData δ P Pd B Bd)
    (c : ℂˣ) (m : ℤ) :
    rationalGammaExpression δ (c / r.coefficient) (m - r.exponent) B Bd =
      rationalGammaExpression δ c m P Pd := by
  have hmon :
      (rationalEpsilonMonomial (c / r.coefficient) (m - r.exponent) :
        RationalFunctions) =
      (rationalEpsilonMonomial c m : RationalFunctions) /
        (rationalEpsilonMonomial r.coefficient r.exponent : RationalFunctions) := by
    simp only [coe_rationalEpsilonMonomial, Units.val_div_eq_div_val, map_div₀,
      zpow_sub₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero)]
    ring
  have hr := r.ratio
  rw [← RatFunc.algebraMap_eq_C, ← coe_rationalEpsilonMonomial] at hr
  simp only [LocalFactor.RationalReflection.subst_polynomial] at hr
  calc
    _ = (rationalEpsilonMonomial (c / r.coefficient) (m - r.exponent) :
          RationalFunctions) *
        (algebraMap ℂ[X] RationalFunctions B /
          aeval (LocalFactor.RationalReflection.reflectedVariable δ) Bd) := by
      unfold rationalGammaExpression
      ring
    _ = _ := by
      rw [hr, hmon]
      unfold rationalGammaExpression
      rw [← mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _
        (rationalEpsilonMonomial r.coefficient r.exponent).ne_zero]

/-- Transfer a rational gamma formula without identifying either whole
polynomial with its block product. -/
theorem HasRationalGammaExpression.of_reflectedRatio
    {δ : ℂˣ} {P Pd B Bd : ℂ[X]} {G : RatFunc ℂ}
    (h : HasRationalGammaExpression δ P Pd G)
    (r : TemperedLFactorGamma.ReflectedRatioData δ P Pd B Bd) :
    HasRationalGammaExpression δ B Bd G := by
  obtain ⟨c, m, hG⟩ := h
  exact ⟨c / r.coefficient, m - r.exponent, hG.trans
    (r.gammaExpression_eq c m).symm⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectedGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance reflectedGammaGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

/-- The inverse-transpose certificate transports to the actual smooth-dual
pair also when the positive ranks are not syntactically successors. -/
theorem isPadicRankLPolynomial_inverseTranspose_iff_smoothContragredient
    {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (GeneralLinear t F.Carrier) W)
    (hπ : IsAdmissible π) (hσ : IsAdmissible σ)
    (hiπ : π.IsIrreducible) (hiσ : σ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : @AdditiveHaarMeasure F.Carrier _ _ (borel F.Carrier))
    {P : ℂ[X]} :
    IsPadicRankLPolynomial F ψ ν
      (π.comp (inverseTranspose n F.Carrier).toMonoidHom)
      (σ.comp (inverseTranspose t F.Carrier).toMonoidHom) P ↔
    IsPadicRankLPolynomial F ψ ν
      (smoothContragredient π) (smoothContragredient σ) P := by
  cases n with
  | zero => exact Iff.rfl
  | succ n =>
    cases t with
    | zero => exact Iff.rfl
    | succ t =>
      exact isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient
        F hπ hσ hiπ hiσ

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  (ψ' : UnitaryAdditiveCharacter F.Carrier)
  (ν' : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ')
  {I : Type uI} {n : I → ℕ}
  {δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
  (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (n i) (δ i))

/-- Actual inverse-transpose certificates give the dual Appendix product.
The smooth dual of a twisted block is admissible and irreducible by the
published cofinal compact-open duality. -/
theorem centeredSegmentFamilyLProduct_of_inverseTransposeCertifiedProduct [Fintype I]
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (hadm : ∀ i, IsAdmissible (δ i).representation)
    (hirr : ∀ i, (δ i).IsIrreducible)
    (s : I → ℝ) {P : ℂ[X]} (Q : I → I → ℂ[X])
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ' ν'.val
      ((realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
          (s i) (δ i).representation).comp (inverseTranspose (n i) F.Carrier).toMonoidHom)
      ((smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation)).comp
        (inverseTranspose (n j) F.Carrier).toMonoidHom) (Q i j))
    (hprod : P = ∏ i, ∏ j, Q i j) :
    IsCenteredSegmentFamilyLProduct F d s P
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
  apply centeredSegmentFamilyLProduct_of_dualCertifiedProduct F ψ ν ψ' ν' d
    hH hEq hadm s Q ?_ hprod
  intro i j
  let A := F.canonicalTopologicalData.segmentFactor (δ i) (s i)
  let B := F.canonicalTopologicalData.segmentFactor (δ j) (s j)
  have hA : A.IsAdmissible :=
    (Langlands.isAdmissible_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (n i) (s i))).mpr
      (hadm i)
  have hB : B.IsAdmissible :=
    (Langlands.isAdmissible_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter (n j) (s j))).mpr
      (hadm j)
  have hiA : A.IsIrreducible := (Langlands.isIrreducible_twist_iff _ _).mpr (hirr i)
  have hiB : B.IsIrreducible := (Langlands.isIrreducible_twist_iff _ _).mpr (hirr j)
  have hBd := (SmoothRep.isAdmissible_contragredient_iff
    (compactOpen_cofinal F F.canonicalTopologicalData (n j)) B).mpr hB
  have hiBd := (SmoothRep.isIrreducible_contragredient_iff
    (compactOpen_cofinal F F.canonicalTopologicalData (n j)) B hB).mpr hiB
  exact (isPadicRankLPolynomial_inverseTranspose_iff_smoothContragredient F
    A.representation B.contragredient.representation hA hBd hiA hiBd ψ' ν'.val).mp (hQ i j)

/-- Block certificates, rather than whole-polynomial product equalities,
identify the gamma germ once gamma multiplicativity supplies a reflected ratio. -/
theorem centeredSegmentFamilyGammaGerm_of_reflectedRatio [Fintype I]
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (hadm : ∀ i, IsAdmissible (δ i).representation)
    (hirr : ∀ i, (δ i).IsIrreducible)
    (s : I → ℝ) {P Pd : ℂ[X]} (Q Qd : I → I → ℂ[X])
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
        (s i) (δ i).representation)
      (smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation)) (Q i j))
    (hQd : ∀ i j, IsPadicRankLPolynomial F ψ' ν'.val
      ((realPowerTwist (F.canonicalTopologicalData.determinantNorm (n i))
          (s i) (δ i).representation).comp (inverseTranspose (n i) F.Carrier).toMonoidHom)
      ((smoothContragredient
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (n j))
          (s j) (δ j).representation)).comp
        (inverseTranspose (n j) F.Carrier).toMonoidHom) (Qd i j))
    {G : RatFunc ℂ}
    (hG : HasRationalGammaExpression (residueReflection F) P Pd G)
    (r : TemperedLFactorGamma.ReflectedRatioData (residueReflection F)
      P Pd (∏ i, ∏ j, Q i j) (∏ i, ∏ j, Qd i j)) :
    ∃ (c : ℂˣ) (m : ℤ), IsCenteredSegmentFamilyGammaGerm F d s G
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal)
      (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m) := by
  classical
  have hL : IsCenteredSegmentFamilyLProductPair F d s
      (∏ i, ∏ j, Q i j) (∏ i, ∏ j, Qd i j)
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) :=
    ⟨centeredSegmentFamilyLProduct_of_certifiedProduct F ψ ν d hH hEq s Q hQ rfl,
      centeredSegmentFamilyLProduct_of_inverseTransposeCertifiedProduct
        F ψ ν ψ' ν' d hH hEq hadm hirr s Qd hQd rfl⟩
  obtain ⟨c, m, hG'⟩ := hG.of_reflectedRatio r
  exact ⟨c, m, hL.gammaGerm F d c m hG'
    (Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j _ => (hQd i j).ne_zero)⟩

end Langlands.RankinSelberg
