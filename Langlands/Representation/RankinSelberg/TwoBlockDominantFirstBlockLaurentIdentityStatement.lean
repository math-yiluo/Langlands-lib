import Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.HarmonicAnalysis.BilateralLaurentSeries

/-!
# The strictly dominant first-block JPSS Laurent identity

JPSS (1983), Section 4.10(2), printed page 419, using the first-block calculation
of Section 4.9, printed pages 416–418. This closed proposition retains the
ordinary Jacquet realization, actual determinant-slice absolute integrability,
and common normalized-generator witnesses for a finite Laurent convolution
identity. It supplies no analytic proof or polynomial cancellation.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The first-block, polynomial-cleared identity for test rank `r + 1` strictly
larger than induced rank `t + 1`. One real bound and one ordinary Jacquet
functional work for every compatible quotient measure and every test. Actual
slice convergence is unconditional in the small-block epsilon certificate;
the certificate supplies common witnesses for the finite Laurent identity. -/
def TwoBlockDominantFirstBlockLaurentIdentityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
      (t r : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (htr : t < r),
    let hlt : m 0 < r := by
      have hsum : m 0 + 1 + (m 1 + 1) = t + 1 := by
        simpa only [Fin.sum_univ_two] using h
      omega
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    let G := GeneralLinear (t + 1) F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let GA := GeneralLinear (m 0 + 1) F.Carrier
    let NA := upperUnipotent (m 0 + 1) F.Carrier
    let NQ := LeftUnipotentQuotient t F.Carrier
    let AQ := LeftUnipotentQuotient (m 0) F.Carrier
    let LQ := TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace GA := borel GA
    letI : BorelSpace GA := ⟨rfl⟩
    letI : MeasurableSpace NA := borel NA
    letI : BorelSpace NA := ⟨rfl⟩
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace AQ := borel AQ
    letI : BorelSpace AQ := ⟨rfl⟩
    letI : MeasurableSpace LQ := borel LQ
    letI : BorelSpace LQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μN : Measure N := unipotentHaar F.Carrier t
    let μGA : Measure GA := generalLinearHaar F.Carrier (m 0)
    let μNA : Measure NA := unipotentHaar F.Carrier (m 0)
    let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
    let q := T.residueCardinality
    let abv := normalizedAbsoluteValue T
    (∃ (hN : Measure.IsMulRightInvariant μN) (hNA : Measure.IsMulRightInvariant μNA),
      letI := hN
      letI := hNA
      (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
      (∃ νA : Measure AQ, IsCompatible NA μGA μNA νA)) ∧
    (∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
      IsOfWhittakerType r (standardCharacter ψ r) π →
      ∀ (lambda : glFunctionals ψ r π)
        {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
        (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
        (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
        ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i),
        ∃ C : ℝ, ∀ u : ℝ, C < u →
          let σu := twoBlockOppositeTwistBlocks F m τ u
          let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
          (∀ f : TwoBlockJacquet.Sections F h σu,
            TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ellu i).val) μR f) ∧
          ∃ J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σu),
            ((∀ i, (ell i).val ≠ 0) → J.val ≠ 0) ∧
            (∀ (f : TwoBlockJacquet.Sections F h σu) (g : G),
              J.val (TwoBlockJacquet.inducedRep F h σu g f) =
                TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
            ∀ (hN : Measure.IsMulRightInvariant μN) (hNA : Measure.IsMulRightInvariant μNA),
              letI := hN
              letI := hNA
              ∀ (νN : Measure NQ) (νA : Measure AQ),
                IsCompatible N μG μN νN → IsCompatible NA μGA μNA νA →
                let νMinus : Measure LQ := Measure.map
                  (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN
                SigmaFinite νN ∧ SigmaFinite νA ∧ SigmaFinite νMinus ∧
                (∀ (j k : ℕ) (hr : r = t + (j + k + 1))
                  (f : TwoBlockJacquet.Sections F h σu)
                  (Wtest : (coefficientModel π lambda).toSubmodule),
                  let Wup : WhittakerFunctions ψ (t + (j + k + 1)) := hr ▸ Wtest.val
                  let Wjac := (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val
                  let μrect := rectangularMeasure ν.val j (t + 1)
                  let μrectBorel :
                    @Measure (Matrix (Fin j) (Fin (t + 1)) F.Carrier) (borel _) := by
                    have hB : (inferInstance :
                        MeasurableSpace (Matrix (Fin j) (Fin (t + 1)) F.Carrier)) = borel _ :=
                      @BorelSpace.measurable_eq _ _ _
                        (inferInstanceAs (BorelSpace (Fin j → Fin (t + 1) → F.Carrier)))
                    exact hB ▸ μrect
                  let A : NQ → ℂ := unequalRankAverage F j k ψ μrectBorel Wup Wjac 0
                  let K : LQ → ℂ :=
                    TwoBlockDominantRectangular.quotientKernel ν.val ellu f Wtest.val hr 0
                  let Nprofile : LQ → ℝ :=
                    TwoBlockDominantRectangular.quotientNormProfile ν.val ellu f Wtest.val hr 0
                  let Fiber : LQ → Prop :=
                    TwoBlockDominantRectangular.quotientFiberIntegrable ν.val ellu f Wtest.val hr 0
                  Measurable A ∧ Measurable K ∧
                  ∀ a : ℤ,
                    Integrable (fun z : NQ × Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
                      unequalRankIntegrand ψ abv j k Wup Wjac 0 z.2 z.1)
                      ((νN.restrict (RankinSelberg.determinantSlice T t a)).prod μrect) ∧
                    Integrable K
                      (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a)) ∧
                    Integrable Nprofile
                      (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a)) ∧
                    ∀ᵐ z ∂νMinus.restrict
                      (TwoBlockLowerUnipotentQuotient.determinantSlice F h a), Fiber z) ∧
                (∀ (cε : ℂˣ) (d : ℤ),
                  UnequalRankEpsilonEquation hlt q ψ abv νA ν.val
                    π (σu 0) lambda (ellu 0) cε d →
                  ∃ (ζ : ℂˣ) (P Pdual : Polynomial ℂ),
                    HasModelMinusOneScalar (σu 0) (ellu 0) ζ ∧
                    (∀ (jsmall ksmall : ℕ)
                      (hrsmall : r = m 0 + (jsmall + ksmall + 1)),
                      IsNormalizedGenerator
                        (unequalRankValuesAt jsmall ksmall hrsmall q ψ abv νA
                          (rectangularMeasure ν.val jsmall (m 0 + 1))
                          π (σu 0) lambda (ellu 0)) P ∧
                      IsNormalizedGenerator
                        (dualUnequalRankRationalValuesAt hlt jsmall ksmall hrsmall
                          q ψ abv νA ν.val π (σu 0) lambda (ellu 0)) Pdual ∧
                      ∀ fsmall : (coefficientModel π lambda).toSubmodule,
                      ∀ ffirst : (coefficientModel (σu 0) (ellu 0)).toSubmodule,
                        ∃ R Rdual : RationalFunctions,
                          HasRationalContinuation q
                            (unequalRankIntegralAt jsmall ksmall hrsmall ψ abv νA
                              (rectangularMeasure ν.val jsmall (m 0 + 1))
                              fsmall.val ffirst.val) R ∧
                          HasRationalContinuation q
                            (dualUnequalRankModelIntegralAt hlt jsmall ksmall hrsmall
                              ψ abv νA ν.val π (σu 0) lambda (ellu 0) fsmall ffirst) Rdual ∧
                          NormalizedFunctionalEquation q P Pdual ζ cε r d R Rdual) ∧
                    ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
                      (f : TwoBlockJacquet.Sections F h σu)
                      (Wtest : (coefficientModel π lambda).toSubmodule),
                      let Wup : WhittakerFunctions ψ (t + (j + k + 1)) := hr ▸ Wtest.val
                      let Wjac := (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val
                      let μrect := rectangularMeasure ν.val j (t + 1)
                      let μrectBorel :
                        @Measure (Matrix (Fin j) (Fin (t + 1)) F.Carrier) (borel _) := by
                        have hB : (inferInstance :
                            MeasurableSpace (Matrix (Fin j) (Fin (t + 1)) F.Carrier)) = borel _ :=
                          @BorelSpace.measurable_eq _ _ _
                            (inferInstanceAs (BorelSpace (Fin j → Fin (t + 1) → F.Carrier)))
                        exact hB ▸ μrect
                      let K : LQ → ℂ :=
                        TwoBlockDominantRectangular.quotientKernel ν.val ellu f Wtest.val hr 0
                      let Zup : BilateralLaurentSeries :=
                        unequalRankSliceCoefficient F j k ψ νN μrectBorel Wup Wjac
                      let Zlow : BilateralLaurentSeries := fun a =>
                        ∫ z, K z
                          ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a)
                      let D : LaurentPolynomial ℂ := Polynomial.eval₂ LaurentPolynomial.C
                        (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1)) Pdual
                      D • Zlow =
                        (LaurentPolynomial.C ((ζ : ℂ) ^ r * (cε : ℂ)) *
                          LaurentPolynomial.T d * P.toLaurent) • Zup))

end Langlands.RankinSelberg
