import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanionProof

/-!
# Lower quotient duality and Fourier coefficient transport

This module states the actual quotient and Fourier comparison of JPSS (1983),
Section 4.8(2)–(4), printed p.415, for the lower integrand of Section 4.7(1).
One geometric homeomorphism precedes all analytic inputs and preserves the
transports of every compatible standard quotient measure. The integrand and
coefficient comparisons are conditional on the explicit scalar identity for
the supplied actual lower sections. This module defines a proposition; it
does not prove the transport or construct a dual-section equivalence.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open TwoBlockLowerUnipotentQuotient

universe uF uW

/-- The Section 4.8 lower-quotient Fourier comparison, with uniform geometric
duality, every compatible quotient measure, the supplied self-dual additive
measure, and actual reversed-dual block sections satisfying the scalar premise.
Both block sizes are positive; no nonzero-functional, smoothness, coefficient
image, Whittaker-type or integrability assumption is imposed. -/
def TwoBlockLowerFourierTransportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let mD : Fin 2 → ℕ := fun i => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 := reverse_sum h
    letI := T.generalLinearTopologicalGroup (t + 1)
    let G := GeneralLinear (t + 1) F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let NQ := LeftUnipotentQuotient t F.Carrier
    let HQ := LowerQuotient h F.Carrier
    let HQD := LowerQuotient hD F.Carrier
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace HQD := borel HQD
    letI : BorelSpace HQD := ⟨rfl⟩
    let Tdual : G → G := fun g =>
      weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g
    ∃ D : HQ ≃ₜ HQD,
      (∀ g : G, D (Quotient.mk _ g) = Quotient.mk _ (Tdual g)) ∧
      (∀ g : G, D.symm (Quotient.mk _ g) = Quotient.mk _ (Tdual g)) ∧
      (∀ z : HQ, TwoBlockLowerUnipotentQuotient.determinantOrder F hD (D z) = -TwoBlockLowerUnipotentQuotient.determinantOrder F h z) ∧
      (∀ z : HQD, TwoBlockLowerUnipotentQuotient.determinantOrder F h (D.symm z) = -TwoBlockLowerUnipotentQuotient.determinantOrder F hD z) ∧
      (∀ k : ℤ,
        D '' TwoBlockLowerUnipotentQuotient.determinantSlice F h k = TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k) ∧
        D ⁻¹' TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k) = TwoBlockLowerUnipotentQuotient.determinantSlice F h k ∧
        D.symm '' TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k) = TwoBlockLowerUnipotentQuotient.determinantSlice F h k ∧
        D.symm ⁻¹' TwoBlockLowerUnipotentQuotient.determinantSlice F h k = TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k)) ∧
      (∀ g : G,
        lowerToStandard hD F.Carrier
            (D ((lowerToStandard h F.Carrier).symm (Quotient.mk _ g))) =
          (Quotient.mk _ (Tdual g) : NQ)) ∧
      (let μG : Measure G := generalLinearHaar F.Carrier t
       let μN : Measure N := unipotentHaar F.Carrier t
       ∀ hN : Measure.IsMulRightInvariant μN,
         letI := hN
         ∀ νN : Measure NQ, IsCompatible N μG μN νN →
           let νMinus : Measure HQ :=
             Measure.map (lowerToStandard h F.Carrier).symm νN
           let νMinusD : Measure HQD :=
             Measure.map (lowerToStandard hD F.Carrier).symm νN
           MeasurePreserving D νMinus νMinusD ∧
           MeasurePreserving D.symm νMinusD νMinus ∧
           ∀ k : ℤ,
             Measure.map D (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) =
               νMinusD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k)) ∧
             Measure.map D.symm (νMinusD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k))) =
               νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) ∧
      ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
        let ψD := ψ.scale (-1)
        ∀ Wtest : WhittakerFunctions ψ t,
          ∃ Wdual : WhittakerFunctions ψD t,
            (∀ g : G, Wdual.val g = Wtest.val (Tdual g)) ∧
            (∀ g : G,
              Wdual.val (blockRotation hD F.Carrier * Tdual g) =
                Wtest.val (blockRotation h F.Carrier * g)) ∧
            ∀ ν : AdditiveHaarMeasure F.Carrier, IsSelfDual ψ ν →
              ∀ Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier),
                IsRowFourierPair ψ ν Φ Φhat →
                (∀ g : G,
                  TwoBlockLowerUnfolding.partialSection hD ψD ν Φhat (Tdual g) =
                    (T.normalizedAbs (determinant g : F.Carrier) : ℂ) *
                      TwoBlockLowerUnfolding.partialSection h ψ ν Φ g) ∧
                ∀ (W : Fin 2 → Type uW)
                  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
                  (σ : ∀ i, Representation ℂ
                    (GeneralLinear (m i + 1) F.Carrier) (W i))
                  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)),
                  let WD : Fin 2 → Type uW := fun i => W i.rev
                  let σD : ∀ i, Representation ℂ
                      (GeneralLinear (mD i + 1) F.Carrier) (WD i) :=
                    fun i => inverseTransposePullback (σ i.rev)
                  let ellD : ∀ i, glInverseFunctionals ψD (mD i) (σD i) :=
                    fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev)
                  ∀ (f : TwoBlockJacquet.Sections F h σ)
                    (fD : TwoBlockJacquet.Sections F hD σD),
                    (∀ g : G,
                      TwoBlockJacquet.scalarSection (fun i => (ellD i).val)
                          fD (Tdual g) 1 =
                        TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1) →
                    let E : HQ → ℂ :=
                      TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν
                    let ED : HQD → ℂ :=
                      TwoBlockLowerUnfolding.integrand ellD fD Wdual Φhat ν
                    (∀ g : G,
                      TwoBlockLowerUnfolding.groupIntegrand ellD fD Wdual Φhat ν
                          (Tdual g) =
                        (T.normalizedAbs (determinant g : F.Carrier) : ℂ) *
                          TwoBlockLowerUnfolding.groupIntegrand ell f Wtest Φ ν g) ∧
                    (∀ z : HQ,
                      ED (D z) =
                        (((T.residueCardinality : ℝ) ^
                            (-TwoBlockLowerUnipotentQuotient.determinantOrder F h z) : ℝ) : ℂ) * E z) ∧
                    (let μG : Measure G := generalLinearHaar F.Carrier t
                     let μN : Measure N := unipotentHaar F.Carrier t
                     ∀ hN : Measure.IsMulRightInvariant μN,
                       letI := hN
                       ∀ νN : Measure NQ, IsCompatible N μG μN νN →
                         let νMinus : Measure HQ :=
                           Measure.map (lowerToStandard h F.Carrier).symm νN
                         let νMinusD : Measure HQD :=
                           Measure.map (lowerToStandard hD F.Carrier).symm νN
                         ∀ k : ℤ,
                           (Integrable ED
                               (νMinusD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k))) ↔
                             Integrable E
                               (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k))) ∧
                           (∫ z, ED z
                               ∂νMinusD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k))) =
                             (T.residueCardinality : ℂ) ^ (-k) *
                               (∫ z, E z
                                 ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) ∧
                           (∫ z, ‖ED z‖
                               ∂νMinusD.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F hD (-k))) =
                             (T.residueCardinality : ℝ) ^ (-k) *
                               (∫ z, ‖E z‖
                                 ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)))

end Langlands.RankinSelberg
