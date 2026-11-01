import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients
import Langlands.Representation.RankinSelberg.TwoBlockSmallFunctionalEquationLaurentBridge
import Langlands.Representation.RankinSelberg.EpsilonFactor

/-!
# The first-block Laurent identity at a representative

At a representative `g` where the iterated upper fiber integrals converge absolutely, the
reflected dual normalized generator applied to the lower coefficients equals the epsilon
monomial times the normalized generator applied to the upper coefficients. Both sides are
row integrals over the last rectangle row `x`; for each `x` the published small functional
equation of the translate by `R(0; x) g` and the first-block coefficient function of `f(g)`
supplies the identity of coefficient functions.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFirstBlockQuotient HarmonicAnalysis
  HarmonicAnalysis.TwoBlockRowPartialFourier QuotientIntegration Whittaker
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

/-- The coefficientwise first-block identity at a representative. -/
theorem pointwise_laurent_identity (hlt : m 0 < t) (hr : t = m 0 + (m 1 + 0 + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
    (lambda : letI := F.canonicalTopologicalData.topology; glFunctionals ψ t π)
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      (coefficientModel π lambda).toSubmodule)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (Kf : (Fin (m 0 + 1) → F.Carrier) → LeftUnipotentQuotient (m 0) F.Carrier → ℂ) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (m 0 + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (m 0 + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (m 0 + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (m 0 + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
    ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA],
      IsCompatible (upperUnipotent (m 0 + 1) F.Carrier) (generalLinearHaar F.Carrier (m 0))
        (unipotentHaar F.Carrier (m 0)) νA →
      ∀ (ν : AdditiveHaarMeasure F.Carrier) (ζ cε : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ),
      IsOfWhittakerType t (standardCharacter ψ t) π →
      IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σ 0) →
      lambda.val ≠ 0 → (ell 0).val ≠ 0 →
      IsNormalizedGenerator
        (unequalRankValuesAt (m 1) 0 hr T.residueCardinality ψ (normalizedAbsoluteValue T) νA
          (rectangularMeasure ν (m 1) (m 0 + 1)) π (σ 0) lambda (ell 0)) P →
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hlt (m 1) 0 hr T.residueCardinality ψ
          (normalizedAbsoluteValue T) νA ν π (σ 0) lambda (ell 0)) Pdual →
      (∀ (fs : (coefficientModel π lambda).toSubmodule)
        (ff : (coefficientModel (σ 0) (ell 0)).toSubmodule),
        ∃ R Rdual : RationalFunctions,
          HasRationalContinuation T.residueCardinality
            (unequalRankIntegralAt (m 1) 0 hr ψ (normalizedAbsoluteValue T) νA
              (rectangularMeasure ν (m 1) (m 0 + 1)) fs.val ff.val) R ∧
          HasRationalContinuation T.residueCardinality
            (dualUnequalRankModelIntegralAt hlt (m 1) 0 hr ψ (normalizedAbsoluteValue T) νA ν
              π (σ 0) lambda (ell 0) fs ff) Rdual ∧
          NormalizedFunctionalEquation T.residueCardinality P Pdual ζ cε t d R Rdual) →
      ∀ g : GeneralLinear (t + 1) F.Carrier,
      (∀ x v, Kf x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0)) →
      (∀ x q, ‖Kf x q‖ ≤ 1) →
      (∀ k : ℤ, AEStronglyMeasurable (Function.uncurry Kf)
        ((rowMeasure ν (m 0 + 1)).prod (νA.restrict (determinantSlice T (m 0) k)))) →
      (∀ k : ℤ, AEStronglyMeasurable
        (Function.uncurry fun Z q =>
          TwoBlockUnfolding.integrand ell f Wtest.val Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)))
        ((rectangularMeasure ν (m 1 + 1) (m 0 + 1)).prod
          (νA.restrict (determinantSlice T (m 0) k)))) →
      (∀ k : ℤ, (∫⁻ Z, ∫⁻ q, ‖TwoBlockUnfolding.integrand ell f Wtest.val Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g))‖ₑ
          ∂νA.restrict (determinantSlice T (m 0) k)
          ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ≠ ⊤) →
      let SL : BilateralLaurentSeries := fun k =>
        (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
          ∫ q in determinantSlice T (m 0) k,
            TwoBlockLowerUnfolding.integrand ell f Wtest.val Φ ν
              (firstBlockFiberPoint F h q g) ∂νA
      let SU : BilateralLaurentSeries := fun k =>
        ∫ Z, ∫ q, TwoBlockUnfolding.integrand ell f Wtest.val Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g))
            ∂νA.restrict (determinantSlice T (m 0) k)
            ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)
      reflectedPolynomial T.residueCardinality Pdual • SL =
        (LaurentPolynomial.C ((ζ : ℂ) ^ t * (cε : ℂ)) * LaurentPolynomial.T d *
            P.toLaurent) • SU := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (m 0 + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (m 0 + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (m 0 + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (m 0 + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
  intro νA _ hνA ν ζ cε d P Pdual hπ hσ hlam hell hP hPd hpairs g hKf hKle hKm hH hfin SL SU
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hr' : t = m 0 + (0 + m 1 + 1) := by omega
  let Q : LaurentPolynomial ℂ := LaurentPolynomial.C ((ζ : ℂ) ^ t * (cε : ℂ)) *
    LaurentPolynomial.T d * P.toLaurent
  let a : (coefficientModel π lambda).toSubmodule →
      (coefficientModel (σ 0) (ell 0)).toSubmodule → BilateralLaurentSeries :=
    fun fs ff n => unequalRankSliceCoefficientAt F (m 1) 0 hr ψ νA
      (rectangularMeasure ν (m 1) (m 0 + 1)) fs.val ff.val n
  let a' : (coefficientModel π lambda).toSubmodule →
      (coefficientModel (σ 0) (ell 0)).toSubmodule → BilateralLaurentSeries :=
    fun fs ff n => unequalRankSliceCoefficientAt F 0 (m 1) hr' (ψ.scale (-1)) νA
      (rectangularMeasure ν 0 (m 0 + 1))
      (translateWhittaker (ψ.scale (-1)) t (firstDualFunction ψ t fs.val)
        (blockWeylAt (m 0) t hlt))
      (secondDualFunction ψ (m 0) ff.val) n
  have hFE : ∀ fs ff, reflectedPolynomial T.residueCardinality Pdual •
      reflectSeries T.residueCardinality (a' fs ff) = Q • a fs ff := by
    intro fs ff
    obtain ⟨R, Rd, hR, hRd, hNFE⟩ := hpairs fs ff
    have hRm : R ∈ unequalRankValuesAt (m 1) 0 hr T.residueCardinality ψ
        (normalizedAbsoluteValue T) νA (rectangularMeasure ν (m 1) (m 0 + 1)) π (σ 0)
        lambda (ell 0) := by
      rw [unequalRankValuesAt_eq]
      exact ⟨fs, ff, hR⟩
    have hRdm : Rd ∈ dualUnequalRankRationalValuesAt hlt (m 1) 0 hr T.residueCardinality ψ
        (normalizedAbsoluteValue T) νA ν π (σ 0) lambda (ell 0) := ⟨fs, ff, hRd⟩
    exact smallFE_coefficient_identity T.residueCardinality_gt_one hP hPd hRm hRdm hR hRd hNFE
      (smallIntegral_series F (m 1) 0 hr ψ νA hνA inferInstance ν π (σ 0) hπ hσ lambda
        (ell 0) hlam hell fs ff)
      (dualSmallIntegral_series F hlt (m 1) 0 hr ψ νA hνA inferInstance ν π (σ 0) hπ hσ
        lambda (ell 0) hlam hell fs ff)
  let Φ' : (Fin (m 0 + 1) → F.Carrier) → ℂ := fun x =>
    Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
  let Wx : (Fin (m 0 + 1) → F.Carrier) → (coefficientModel π lambda).toSubmodule := fun x =>
    modelRepresentation π lambda (lowerRadical h F.Carrier (rowSnoc 0 x) * g) Wtest
  let Fg := firstBlockCoefficient ell f g
  have hU : ∀ k : ℤ, Integrable (fun x => Φ' x * a (Wx x) Fg k) (rowMeasure ν (m 0 + 1)) ∧
      SU k = ∫ x, Φ' x * a (Wx x) Fg k ∂rowMeasure ν (m 0 + 1) := fun k =>
    upper_coefficient_eq_rowIntegral hr ell f Wtest.val Φ νA ν k g (hH k) (hfin k)
  have hS : ∀ k : ℤ, Integrable (fun x => Φ' x *
        reflectSeries T.residueCardinality (a' (Wx x) Fg) k) (rowMeasure ν (m 0 + 1)) ∧
      SL k = ∫ x, Φ' x * reflectSeries T.residueCardinality (a' (Wx x) Fg) k
        ∂rowMeasure ν (m 0 + 1) := by
    intro k
    let Wg := modelRepresentation π lambda g Wtest
    have hG := dualIntegrand_integrableOn_slice F hlt (m 1) 0 hr ψ νA hνA inferInstance ν π (σ 0)
      hπ hσ lambda (ell 0) hlam hell Wg Fg (-k)
    have hmp := (measurePreserving_reflectionQuotient F (m 0) νA hνA).restrict_preimage
      (measurableSet_determinantSlice T (m 0) (-k))
    have hpre : reflectionQuotient (m 0) ⁻¹' determinantSlice T (m 0) (-k) =
        determinantSlice T (m 0) k := Set.ext fun q => by
      rw [Set.mem_preimage, reflectionQuotient_mem_determinantSlice F (m 0) (-k), neg_neg]
    rw [hpre] at hmp
    have hA := (hmp.integrable_comp_emb (reflectionQuotient (m 0)).measurableEmbedding).mpr hG
    exact lower_coefficient_eq_rowIntegral hlt hr' ell f Wtest.val Φ Kf νA hνA ν k g hKf
      (hKm k) hKle hA
  have eqL : SL = BilateralLaurentSeries.coeffwiseIntegral (rowMeasure ν (m 0 + 1))
      (fun x => Φ' x • reflectSeries T.residueCardinality (a' (Wx x) Fg)) := by
    funext k
    exact (hS k).2
  have eqU : SU = BilateralLaurentSeries.coeffwiseIntegral (rowMeasure ν (m 0 + 1)) (fun x => Φ' x • a (Wx x) Fg) := by
    funext k
    exact (hU k).2
  rw [eqL, eqU]
  refine integral_laurent_identity_ae _ _ (fun n => (hS n).1) (fun n => (hU n).1)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [smul_comm _ (Φ' x), smul_comm Q (Φ' x), hFE]

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
