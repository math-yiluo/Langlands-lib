import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.GL.CountabilityProof
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Normalized integration for the two-block unipotent quotient tower

Derived analytic infrastructure for the first unfolding of JPSS (1983),
Section 4.6, printed pages 411-412. The subgroup and quotient maps are the
published actual objects. The rectangular additive Haar measure is supplied
unchanged, with its integral-cube mass retained as the factor in the measure,
Tonelli and Bochner identities. This module states, but does not prove, the
quotient-measure existence, fiber-kernel and absolute-integrability assertions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration TwoBlockUnipotentQuotient
open scoped ENNReal ProbabilityTheory

universe uF

/-- Normalized integration along `H \\ G → N \\ G`, where `H` is the block-diagonal
unipotent subgroup, for every supplied rectangular additive Haar measure.
The factor is its positive finite integral-cube mass. The conclusions include
compatible quotient existence, a measurable s-finite fiber kernel, restricted
measure and Tonelli identities, and absolute-integrability and Bochner laws. -/
def TwoBlockUnipotentQuotientIntegrationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    let G := GeneralLinear (t + 1) F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let H := blockUnipotent h F.Carrier
    let NQ := LeftUnipotentQuotient t F.Carrier
    let HQ := BlockQuotient h F.Carrier
    let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    letI : BorelSpace H := ⟨rfl⟩
    letI : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
      fun i => borel (upperUnipotent (m i + 1) F.Carrier)
    letI : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) :=
      fun _ => ⟨rfl⟩
    letI : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
      fun i => by
        let := T.generalLinearSecondCountableTopology (m i + 1)
        exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    -- These Borel instances use the actual finite product measurable spaces.
    letI : BorelSpace (BlockUnipotents m F.Carrier) := inferInstance
    letI : BorelSpace R := inferInstance
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μN : Measure N := unipotentHaar F.Carrier t
    let μH : Measure H := Measure.map (blockUnipotentEquiv h F.Carrier)
      (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i)))
    μH.IsHaarMeasure ∧ μH.Regular ∧
      ∃ (hN : Measure.IsMulRightInvariant μN) (hH : Measure.IsMulRightInvariant μH),
        letI := hN
        letI := hH
        (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
        (∃ νH : Measure HQ, IsCompatible H μG μH νH) ∧
        ∀ (μR : Measure R) [μR.IsAddHaarMeasure],
          let O := (ValuativeRel.valuation F.Carrier).integer
          let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ O}
          0 < c ∧ c < ⊤ ∧
            ∃ (κ : ProbabilityTheory.Kernel NQ HQ)
              (_hκ : ProbabilityTheory.IsSFiniteKernel κ),
              (∀ g : G, κ (Quotient.mk _ g) =
                Measure.map (fun x => fiberPoint h F.Carrier x g) μR) ∧
              ∀ (νN : Measure NQ) (νH : Measure HQ),
                IsCompatible N μG μN νN → IsCompatible H μG μH νH →
                SigmaFinite νN ∧ SigmaFinite νH ∧
                ∀ s : Set NQ, MeasurableSet s →
                  let νNs := νN.restrict s
                  let νHs := νH.restrict (projection h F.Carrier ⁻¹' s)
                  (κ ∘ₘ νNs = c • νHs) ∧
                  (∀ f : HQ → ℝ≥0∞, Measurable f →
                    (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νNs) = c * ∫⁻ z, f z ∂νHs) ∧
                  (∀ f : HQ → ℂ, Measurable f →
                    (Integrable f νHs ↔
                      (∀ᵐ q ∂νNs, Integrable f (κ q)) ∧
                      Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νNs) ∧
                    (Integrable f νHs →
                      Integrable (radicalAverage F h μR f) νNs ∧
                      (∫ q, radicalAverage F h μR f q ∂νNs) =
                        c.toReal • (∫ z, f z ∂νHs)))

end Langlands.RankinSelberg
