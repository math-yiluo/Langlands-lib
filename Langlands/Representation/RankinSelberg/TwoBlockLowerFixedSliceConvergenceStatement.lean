import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement

/-!
# Absolute convergence on every determinant slice of the Section 4.7 lower quotient

JPSS (1983), Section 4.7, printed pages 412–414. This proposition states absolute
convergence of the actual descended lower integrand for sufficiently large opposite
real twists. The bound follows the full Whittaker-type test representation and the
supplied functionals and precedes the real parameter, quotient measure, section,
coefficient, row Schwartz function and determinant-slice integer.

Compatible standard quotient measures exist for the exact normalized group and
unipotent Haar measures. Every compatible measure and its transport by the inverse
of `[g] ↦ [Crot * g]` are sigma-finite. On each slice the proposition asserts
measurability, both absolute-integrability conclusions, and the complex and norm
integral transport identities. This is a statement, not a proof of convergence.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Fixed-determinant-slice absolute convergence of the unweighted integrand in
JPSS (4.7.1), with the supplied self-dual Fourier measure and the lower quotient
measure transported from every compatible standard quotient measure. Full standard
Whittaker type is assumed for the test representation and both blocks; all supplied
functionals, including zero, and all actual coefficient-image vectors are retained.
The single real bound may depend on the test representation and all preceding data. -/
def TwoBlockLowerFixedSliceConvergenceStatement : Prop :=
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
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    letI := T.generalLinearTopologicalGroup (t + 1)
    let G := GeneralLinear (t + 1) F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let NQ := LeftUnipotentQuotient t F.Carrier
    let HQ := TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μN : Measure N := unipotentHaar F.Carrier t
    ∃ hN : Measure.IsMulRightInvariant μN,
      letI := hN
      (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
      (∀ νN : Measure NQ, IsCompatible N μG μN νN →
        SigmaFinite νN ∧
          SigmaFinite (Measure.map
            (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN)) ∧
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ G V),
        IsOfWhittakerType t (standardCharacter ψ t) π →
        ∀ (lambda : glFunctionals ψ t π)
          {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
          (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
          (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
          ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i),
          ∃ C : ℝ, ∀ u : ℝ, C < u →
            ∀ νN : Measure NQ, IsCompatible N μG μN νN →
              let νMinus : Measure HQ := Measure.map
                (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN
              ∀ (f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u))
                (Wtest : (coefficientModel π lambda).toSubmodule)
                (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)) (k : ℤ),
                let E : HQ → ℂ := TwoBlockLowerUnfolding.integrand
                  (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
                  f Wtest.val Φ ν.val
                let Estandard : NQ → ℂ := fun q =>
                  E ((TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm q)
                let lowerSlice := TwoBlockLowerUnipotentQuotient.determinantSlice F h k
                let standardSlice := RankinSelberg.determinantSlice T t k
                Measurable E ∧
                Integrable E (νMinus.restrict lowerSlice) ∧
                Integrable Estandard (νN.restrict standardSlice) ∧
                (∫ z, E z ∂νMinus.restrict lowerSlice) =
                  (∫ q, Estandard q ∂νN.restrict standardSlice) ∧
                (∫ z, ‖E z‖ ∂νMinus.restrict lowerSlice) =
                  (∫ q, ‖Estandard q‖ ∂νN.restrict standardSlice)

end Langlands.RankinSelberg
