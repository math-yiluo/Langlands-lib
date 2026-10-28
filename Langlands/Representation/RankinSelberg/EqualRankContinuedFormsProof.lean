import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsStatement
import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalField.Normalization.Proof
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.EqualRankContinuationFamily

/-!
# Construction of the continued normalized equal-rank trilinear forms

The cleared rational continuations of the original and Fourier-dual equal-rank
integrals have unique Laurent lifts, linear in the test triple. Evaluating them at
the nonzero spectral points `q^(-s)` and `q^(-(1-s))` gives trilinear forms for
every complex parameter. Their twisted invariance follows from the monomial
translation laws of the lifts, and they agree with the normalized rational
continuations wherever the relevant continuation is regular.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section RowFourierMap

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {d : ℕ} [BorelSpace (Fin d → F)]
  {ψ : UnitaryAdditiveCharacter F} {ν : AdditiveHaarMeasure F} [SigmaFinite ν.measure]

/-- The row Fourier transform on Schwartz--Bruhat functions, selected from the
closure hypothesis. Its values are unique, so it is complex-linear. -/
def rowFourierMap (h : RowFourierClosed ψ ν d) :
    SchwartzBruhat (Fin d → F) →ₗ[ℂ] SchwartzBruhat (Fin d → F) where
  toFun Φ := Classical.choose (h Φ)
  map_add' Φ₁ Φ₂ := by
    refine IsRowFourierPair.unique (Classical.choose_spec (h (Φ₁ + Φ₂))) fun y => ?_
    change (Classical.choose (h Φ₁)) y + (Classical.choose (h Φ₂)) y = _
    rw [Classical.choose_spec (h Φ₁) y, Classical.choose_spec (h Φ₂) y]
    exact (congrFun ((rowFourierTransform ψ ν).map_add Φ₁ Φ₂) y).symm
  map_smul' c Φ := by
    refine IsRowFourierPair.unique (Classical.choose_spec (h (c • Φ))) fun y => ?_
    change c * (Classical.choose (h Φ)) y = _
    rw [Classical.choose_spec (h Φ) y]
    exact (congrFun ((rowFourierTransform ψ ν).map_smul c Φ) y).symm

theorem isRowFourierPair_rowFourierMap (h : RowFourierClosed ψ ν d)
    (Φ : SchwartzBruhat (Fin d → F)) : IsRowFourierPair ψ ν Φ (rowFourierMap h Φ) :=
  Classical.choose_spec (h Φ)

theorem eq_rowFourierMap (h : RowFourierClosed ψ ν d)
    {Φ Φhat : SchwartzBruhat (Fin d → F)} (hp : IsRowFourierPair ψ ν Φ Φhat) :
    Φhat = rowFourierMap h Φ :=
  IsRowFourierPair.unique hp (isRowFourierPair_rowFourierMap h Φ)

/-- The Fourier transform of a right translate is a scalar multiple of the
inverse-transpose translate of the Fourier transform. -/
theorem rowFourierMap_translate (h : RowFourierClosed ψ ν d) (abv : AbsoluteValue F ℝ)
    (hequiv : ∀ (g : Langlands.GeneralLinear d F) (Φ Φg : SchwartzBruhat (Fin d → F)),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) → ∀ y,
        rowFourierIntegral ψ ν d Φg y = ((abv (Matrix.det g.val) : ℂ)⁻¹) *
          rowFourierIntegral ψ ν d Φ (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)))
    (g : Langlands.GeneralLinear d F) (Φ Φg Ψ : SchwartzBruhat (Fin d → F))
    (hΦg : ∀ x, Φg x = Φ (Matrix.vecMul x g.val))
    (hΨ : ∀ x, Ψ x = rowFourierMap h Φ (Matrix.vecMul x (inverseTranspose d F g).val)) :
    rowFourierMap h Φg = ((abv (Matrix.det g.val) : ℂ)⁻¹) • Ψ := by
  refine (eq_rowFourierMap h fun y => ?_).symm
  change ((abv (Matrix.det g.val) : ℂ)⁻¹) * Ψ y = _
  rw [hequiv g Φ Φg hΦg y, hΨ y, isRowFourierPair_rowFourierMap h Φ, inverseTranspose_coe]

end RowFourierMap

section Determinant

variable {F : Type uF} [Field F] {d : ℕ}

theorem det_inverseTranspose (g : Langlands.GeneralLinear d F) :
    Matrix.det (inverseTranspose d F g).val = (Matrix.det g.val)⁻¹ := by
  rw [inverseTranspose_coe, Matrix.det_transpose]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

theorem abv_det_inverseTranspose (abv : AbsoluteValue F ℝ) (g : Langlands.GeneralLinear d F) :
    abv (Matrix.det (inverseTranspose d F g).val) = (abv (Matrix.det g.val))⁻¹ := by
  rw [det_inverseTranspose, map_inv₀]

end Determinant

section Spectral

/-- The determinant factor of the dual side combines with the reflected spectral
point into the original spectral twist. -/
theorem dual_spectral_factor {q : ℕ} (hq : 0 < q) (m : ℤ) (s : ℂ) :
    ((((q : ℝ) ^ m : ℝ) : ℂ))⁻¹ * spectralPoint q (1 - s) ^ (-m) =
      spectralPoint q s ^ m := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [spectralPoint, Complex.cpow_neg, Complex.ofReal_zpow, Complex.ofReal_natCast]
  rw [Complex.cpow_sub _ _ hq0, Complex.cpow_one, inv_zpow', neg_neg, div_zpow, div_eq_mul_inv,
    inv_mul_cancel_left₀ (zpow_ne_zero m hq0), inv_zpow]

end Spectral

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The normalized absolute value of the determinant of an invertible matrix is
an integer power of the residue cardinality. -/
theorem normalizedAbsoluteValue_det_eq_zpow {d : ℕ}
    (g : Langlands.GeneralLinear d F.Carrier) :
    normalizedAbsoluteValue T (Matrix.det g.val) =
      (T.residueCardinality : ℝ) ^ (-T.ord (Matrix.det g.val)) := by
  rw [normalizedAbsoluteValue_apply,
    T.normalizedAbs_of_ne_zero (Matrix.isUnits_det_units g).ne_zero]

/-- The p-adic row Fourier equivariance, read in the instance context of the
continued-forms statement with the normalized absolute value. -/
theorem padic_rowFourier_equivariance (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
    letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (g : Langlands.GeneralLinear (n + 1) F.Carrier)
      (Φ Φg : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) → ∀ y,
        rowFourierIntegral ψ ν (n + 1) Φg y =
          ((normalizedAbsoluteValue T (Matrix.det g.val) : ℂ)⁻¹) *
            rowFourierIntegral ψ ν (n + 1) Φ (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)) := by
  intro ψ ν g Φ Φg hΦg y
  exact (HarmonicAnalysis.padicRowFourierEquivariance F T (n + 1) ψ ν g Φ).2 Φg hΦg y

/-- Right translates of row Schwartz--Bruhat functions exist, in the instance
context of the continued-forms statement (first half of the published
equivariance theorem). -/
theorem padic_row_translate_exists (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (_ψ : UnitaryAdditiveCharacter F.Carrier) (_ν : AdditiveHaarMeasure F.Carrier)
      (g : Langlands.GeneralLinear (n + 1) F.Carrier)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      ∃ Φg : SchwartzBruhat (Fin (n + 1) → F.Carrier), ∀ x, Φg x = Φ (Matrix.vecMul x g.val) := by
  intro ψ ν g Φ
  exact (HarmonicAnalysis.padicRowFourierEquivariance F T (n + 1) ψ ν g Φ).1

/-- Borel structure on rows and sigma-finiteness of the scalar Haar measure in
the instance context of the continued-forms statement. -/
theorem padic_row_instances (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
    letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ ν : AdditiveHaarMeasure F.Carrier,
      BorelSpace (Fin (n + 1) → F.Carrier) ∧ SigmaFinite ν.measure := by
  intro ν
  let := T.topology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  have : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  exact ⟨inferInstance, inferInstance⟩

end Padic

section LaurentSpectral

/-- Evaluating a monomial multiple at the spectral point of `s`. -/
theorem laurentEval_spectralUnit_T_mul {q : ℕ} (hq0 : 0 < q) (m : ℤ) (s : ℂ)
    (a : LaurentCoefficients) :
    laurentEval (spectralUnit hq0 s) (LaurentPolynomial.T m * a) =
      spectralPoint q s ^ m * laurentEval (spectralUnit hq0 s) a := by
  rw [map_mul, laurentEval_T, coe_spectralUnit]

/-- Evaluating the dual translation factor at the spectral point of `1 - s`
gives the original spectral twist. -/
theorem laurentEval_spectralUnit_dual_factor {q : ℕ} (hq0 : 0 < q) (m : ℤ) (s : ℂ)
    (a : LaurentCoefficients) :
    laurentEval (spectralUnit hq0 (1 - s))
        ((((q : ℝ) ^ m : ℝ) : ℂ)⁻¹ • (LaurentPolynomial.T (-m) * a)) =
      spectralPoint q s ^ m * laurentEval (spectralUnit hq0 (1 - s)) a := by
  rw [laurentEval_smul, map_mul, laurentEval_T, coe_spectralUnit, ← dual_spectral_factor hq0 m s]
  ring

end LaurentSpectral

section Assembly

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ψ : UnitaryAdditiveCharacter F} {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
  {q : ℕ} {abv : AbsoluteValue F ℝ}

/-- A Laurent lift of the cleared original continuation family is multiplied by
the monomial `T m` under simultaneous right translation by `g` with
`|det g| = q^m`. -/
theorem laurentLift_translate_original (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (P : Polynomial ℂ)
    (L : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ] (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ]
      SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] LaurentCoefficients)
    (hL : ∀ f f' Φ, laurentToRatFunc (L f f' Φ) =
      algebraMap (Polynomial ℂ) RationalFunctions P * equalRankContinuationFamily hq hA f f' Φ)
    (g : Langlands.GeneralLinear (n + 1) F) (m : ℤ) (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    {Φ Φg : SchwartzBruhat (Fin (n + 1) → F)} (hΦ : ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) :
    L (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg =
      LaurentPolynomial.T m * L f f' Φ := by
  apply laurentToRatFunc_injective
  rw [map_mul, laurentToRatFunc_T, hL, hL,
    equalRankContinuationFamily_translate hq hA hμ g m hg f f' hΦ]
  ring

variable [MeasurableSpace F]

/-- A Laurent lift of the cleared dual continuation family, precomposed with the
dual model maps and the row Fourier transform, is multiplied by
`q^(-m) T(-m)` under simultaneous right translation by `g` with `|det g| = q^m`.
This combines the Fourier equivariance law with the translation law of the dual
family at the inverse transpose of `g`. -/
theorem laurentLift_translate_dual (hq : 1 < q) {ν : AdditiveHaarMeasure F}
    [BorelSpace (Fin (n + 1) → F)] [SigmaFinite ν.measure]
    (hAd : EqualRankAnalyticConclusion q (ψ.scale (-1)) abv μ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (hF : RowFourierClosed ψ ν (n + 1))
    (htrans : ∀ (g : Langlands.GeneralLinear (n + 1) F) (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      ∃ Φg : SchwartzBruhat (Fin (n + 1) → F), ∀ x, Φg x = Φ (Matrix.vecMul x g.val))
    (hequiv : ∀ (g : Langlands.GeneralLinear (n + 1) F)
      (Φ Φg : SchwartzBruhat (Fin (n + 1) → F)),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) → ∀ y,
        rowFourierIntegral ψ ν (n + 1) Φg y = ((abv (Matrix.det g.val) : ℂ)⁻¹) *
          rowFourierIntegral ψ ν (n + 1) Φ (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)))
    (Pd : Polynomial ℂ)
    (Ld : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ] (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ]
      SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] LaurentCoefficients)
    (hLd : ∀ f f' Φ, laurentToRatFunc (Ld f f' Φ) =
      algebraMap (Polynomial ℂ) RationalFunctions Pd * equalRankContinuationFamily hq hAd
        (firstDualModelMap ψ π ℓ f) (secondDualModelMap ψ σ ℓ' f') (rowFourierMap hF Φ))
    (g : Langlands.GeneralLinear (n + 1) F) (m : ℤ) (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    {Φ Φg : SchwartzBruhat (Fin (n + 1) → F)} (hΦ : ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) :
    Ld (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg =
      ((((q : ℝ) ^ m : ℝ) : ℂ))⁻¹ • (LaurentPolynomial.T (-m) * Ld f f' Φ) := by
  obtain ⟨Ψ, hΨ⟩ := htrans (inverseTranspose (n + 1) F g) (rowFourierMap hF Φ)
  have hdet : abv (Matrix.det (inverseTranspose (n + 1) F g).val) = (q : ℝ) ^ (-m) := by
    rw [abv_det_inverseTranspose, hg, zpow_neg]
  have hfourier := rowFourierMap_translate hF abv hequiv g Φ Φg Ψ hΦ hΨ
  rw [hg] at hfourier
  apply laurentToRatFunc_injective
  rw [laurentToRatFunc_smul, map_mul, laurentToRatFunc_T, hLd, hLd,
    firstDualModelMap_modelRepresentation, secondDualModelMap_modelRepresentation,
    hfourier, map_smul, equalRankContinuationFamily_translate hq hAd hμ _ (-m) hdet _ _ hΨ,
    RatFunc.smul_eq_C_mul, RatFunc.smul_eq_C_mul]
  ring

/-- The construction of the continued forms over a general topological field,
from the right-invariance of the quotient measure, integrality of
`log_q |det g|`, existence of right translates of row test functions, and the
Fourier equivariance law. -/
theorem continuedForms_of_laws (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (ν : AdditiveHaarMeasure F) [BorelSpace (Fin (n + 1) → F)] [SigmaFinite ν.measure]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    {q : ℕ} (hq : 1 < q) (abv : AbsoluteValue F ℝ)
    (habv : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∃ m : ℤ, abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (htrans : ∀ (g : Langlands.GeneralLinear (n + 1) F) (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      ∃ Φg : SchwartzBruhat (Fin (n + 1) → F), ∀ x, Φg x = Φ (Matrix.vecMul x g.val))
    (hequiv : ∀ (g : Langlands.GeneralLinear (n + 1) F)
      (Φ Φg : SchwartzBruhat (Fin (n + 1) → F)),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) → ∀ y,
        rowFourierIntegral ψ ν (n + 1) Φg y = ((abv (Matrix.det g.val) : ℂ)⁻¹) *
          rowFourierIntegral ψ ν (n + 1) Φ (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)))
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hAd : EqualRankAnalyticConclusion q (ψ.scale (-1)) abv μ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (hF : RowFourierClosed ψ ν (n + 1)) (P Pd : Polynomial ℂ)
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (hPd : IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') Pd) :
    ∃ B Bdual : ℂ → ((coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
        (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] ℂ),
      (∀ s : ℂ,
        (∀ (g : Langlands.GeneralLinear (n + 1) F) (f : (coefficientModel π ℓ).toSubmodule)
          (f' : (coefficientModel σ ℓ').toSubmodule) (Φ Φg : SchwartzBruhat (Fin (n + 1) → F)),
          (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
            B s (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg =
              determinantWeight abv g (-s) * B s f f' Φ) ∧
        (∀ (g : Langlands.GeneralLinear (n + 1) F) (f : (coefficientModel π ℓ).toSubmodule)
          (f' : (coefficientModel σ ℓ').toSubmodule) (Φ Φg : SchwartzBruhat (Fin (n + 1) → F)),
          (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
            Bdual s (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg =
              determinantWeight abv g (-s) * Bdual s f f' Φ)) ∧
      ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ Φhat : SchwartzBruhat (Fin (n + 1) → F)),
        IsRowFourierPair ψ ν Φ Φhat →
        ∀ R Rd : RationalFunctions,
          HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R →
          HasRationalContinuation q (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat) Rd →
          ∀ s : ℂ,
            (R.denom.eval (spectralPoint q s) ≠ 0 →
              B s f f' Φ = P.eval (spectralPoint q s) *
                RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) ∧
            (Rd.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
              Bdual s f f' Φ = Pd.eval (spectralPoint q (1 - s)) *
                RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  -- The original continuation family and its Laurent lift.
  let Cf := equalRankContinuationFamily hq hA
  have hC : ∀ f f' Φ, ∃ a : LaurentCoefficients, laurentToRatFunc a =
      algebraMap (Polynomial ℂ) RationalFunctions P * Cf f f' Φ :=
    fun f f' Φ => hP.clearsDenominators
      (mem_zetaSpan ⟨f, f', Φ, equalRankContinuationFamily_spec hq hA f f' Φ⟩)
  let L := laurentLift (M := (coefficientModel π ℓ).toSubmodule)
    (M' := (coefficientModel σ ℓ').toSubmodule) (S := SchwartzBruhat (Fin (n + 1) → F)) P Cf hC
  have hL_spec : ∀ f f' Φ, laurentToRatFunc (L f f' Φ) =
      algebraMap (Polynomial ℂ) RationalFunctions P * Cf f f' Φ :=
    laurentLift_spec P Cf hC
  -- The dual continuation family, precomposed with the dual model maps and the
  -- Fourier transform, and its Laurent lift.
  let Cfd := equalRankContinuationFamily hq hAd
  let Cd := trilinearPrecomp (M := (coefficientModel π ℓ).toSubmodule)
    (M' := (coefficientModel σ ℓ').toSubmodule) (S := SchwartzBruhat (Fin (n + 1) → F))
    (N := (coefficientModel (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)).toSubmodule)
    (N' := (coefficientModel (inverseTransposePullback σ)
      (secondDualFunctional ψ σ ℓ')).toSubmodule)
    (U := SchwartzBruhat (Fin (n + 1) → F)) (A := RationalFunctions) Cfd
    (firstDualModelMap ψ π ℓ) (secondDualModelMap ψ σ ℓ') (rowFourierMap hF)
  have hCd_apply : ∀ f f' Φ, Cd f f' Φ = Cfd
      (firstDualModelMap ψ π ℓ f) (secondDualModelMap ψ σ ℓ' f') (rowFourierMap hF Φ) :=
    fun _ _ _ => rfl
  have hCd_spec : ∀ f f' Φ, HasRationalContinuation q
      (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' (rowFourierMap hF Φ)) (Cd f f' Φ) := by
    intro f f' Φ
    rw [dualEqualRankModelIntegral_eq, hCd_apply]
    exact equalRankContinuationFamily_spec hq hAd _ _ _
  have hCd : ∀ f f' Φ, ∃ a : LaurentCoefficients, laurentToRatFunc a =
      algebraMap (Polynomial ℂ) RationalFunctions Pd * Cd f f' Φ :=
    fun f f' Φ => hPd.clearsDenominators (mem_zetaSpan ⟨f, f', rowFourierMap hF Φ, hCd_spec f f' Φ⟩)
  let Ld := laurentLift (M := (coefficientModel π ℓ).toSubmodule)
    (M' := (coefficientModel σ ℓ').toSubmodule) (S := SchwartzBruhat (Fin (n + 1) → F)) Pd Cd hCd
  have hLd_spec : ∀ f f' Φ, laurentToRatFunc (Ld f f' Φ) =
      algebraMap (Polynomial ℂ) RationalFunctions Pd * Cfd
        (firstDualModelMap ψ π ℓ f) (secondDualModelMap ψ σ ℓ' f') (rowFourierMap hF Φ) :=
    fun f f' Φ => by rw [← hCd_apply]; exact laurentLift_spec Pd Cd hCd f f' Φ
  -- From here on only the characterizing properties of the lifts are used.
  clear_value L Ld
  refine ⟨fun s => trilinearPostcomp (M := (coefficientModel π ℓ).toSubmodule)
      (M' := (coefficientModel σ ℓ').toSubmodule) (S := SchwartzBruhat (Fin (n + 1) → F))
      (laurentEval (spectralUnit hq0 s)).toLinearMap L,
    fun s => trilinearPostcomp (M := (coefficientModel π ℓ).toSubmodule)
      (M' := (coefficientModel σ ℓ').toSubmodule) (S := SchwartzBruhat (Fin (n + 1) → F))
      (laurentEval (spectralUnit hq0 (1 - s))).toLinearMap Ld, fun s => ⟨?_, ?_⟩, ?_⟩
  · -- Twisted invariance of the original form.
    intro g f f' Φ Φg hΦ
    obtain ⟨m, hg⟩ := habv g
    simp only [trilinearPostcomp_apply, AlgHom.toLinearMap_apply]
    rw [laurentLift_translate_original hq hA hμ P L hL_spec g m hg f f' hΦ,
      laurentEval_spectralUnit_T_mul, determinantWeight_neg_eq_spectralPoint_zpow hq0 abv g m hg s]
  · -- Twisted invariance of the dual form.
    intro g f f' Φ Φg hΦ
    obtain ⟨m, hg⟩ := habv g
    simp only [trilinearPostcomp_apply, AlgHom.toLinearMap_apply]
    rw [laurentLift_translate_dual hq hAd hμ hF htrans hequiv Pd Ld hLd_spec g m hg f f' hΦ,
      laurentEval_spectralUnit_dual_factor,
      determinantWeight_neg_eq_spectralPoint_zpow hq0 abv g m hg s]
  · -- Evaluation at regular points.
    intro f f' Φ Φhat hpair R Rd hR hRd s
    refine ⟨fun hreg => ?_, fun hreg => ?_⟩
    · have hCR : Cf f f' Φ = R := equalRankContinuationFamily_eq hq hA hR
      simp only [trilinearPostcomp_apply, AlgHom.toLinearMap_apply]
      exact laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq0 s)
        (by rw [hL_spec, hCR]) hreg
    · have hhat := eq_rowFourierMap hF hpair
      have hCR : Cfd (firstDualModelMap ψ π ℓ f) (secondDualModelMap ψ σ ℓ' f')
          (rowFourierMap hF Φ) = Rd := by
        refine equalRankContinuationFamily_eq hq hAd ?_
        rw [← dualEqualRankModelIntegral_eq, ← hhat]
        exact hRd
      simp only [trilinearPostcomp_apply, AlgHom.toLinearMap_apply]
      exact laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq0 (1 - s))
        (by rw [hLd_spec, hCR]) hreg

end Assembly

/-- **Continued normalized equal-rank trilinear forms.** Proof of
`EqualRankContinuedFormsStatement`. -/
theorem equalRankContinuedForms {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : EqualRankContinuedFormsStatement.{uF, uV, uW} F T n := by
  have hequiv := padic_rowFourier_equivariance T n
  have htrans := padic_row_translate_exists T n
  have hinst := padic_row_instances T n
  unfold EqualRankContinuedFormsStatement
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ _ μ hμ ν V _ _ W _ _ π σ _ _ ℓ ℓ' _ _ q abv hA hAd hF P Pd hP hPd M M' S
    IsTwistedInvariant
  obtain ⟨hB, hS⟩ := hinst ν
  exact continuedForms_of_laws ψ μ hμ.right_invariant ν π σ ℓ ℓ' T.residueCardinality_gt_one
    abv (fun g => ⟨_, normalizedAbsoluteValue_det_eq_zpow T g⟩) (htrans ψ ν) (hequiv ψ ν)
    hA hAd hF P Pd hP hPd

end Langlands.RankinSelberg
