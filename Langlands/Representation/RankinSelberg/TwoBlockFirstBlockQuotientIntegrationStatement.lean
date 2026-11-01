import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.GL.CountabilityProof
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Normalized first-block quotient integration on determinant slices

Analytic statement underlying JPSS (1983), Section 4.6, printed page 412, equation (6):

`∫_{N_(t_1,t_2) \ G_r^m} f(g) dg =
  ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a`.

The subgroups, quotients, slices, fiber map and first-block average are the published actual
objects of `TwoBlockFirstBlockQuotientData`. The ambient and subgroup measures are the
published normalized Haar measures, with the Haar measure of `GL_a^0` given by restriction
from `GL_a`; no factor occurs. The kernel packaging and the absolute-integrability
equivalence are derived consequences of the source formula. This module states, but does
not prove, these assertions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration
open scoped ENNReal ProbabilityTheory

universe uF

/-- Normalized disintegration of `H \ G^k` over the zero slice `L \ G^0`, where
`H = N_(t_1,t_2)` is the block-diagonal unipotent subgroup and
`L = diag(GL_a^0, N_b)`, with fibers the small slices `N_a \ GL_a^k` through
`[u] ↦ [diag(u, 1) g]_H`. The measures are the published normalized Haar measures; the
Haar measure of `GL_a^0` is the restriction of that of `GL_a`. The conclusions include
compatible quotient existence, sigma-finiteness, a measurable s-finite fiber kernel for each
`k`, the restricted measure and Tonelli identities, and absolute-integrability and Bochner
laws for the published first-block average. -/
def TwoBlockFirstBlockQuotientIntegrationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    let G := GeneralLinear (t + 1) F.Carrier
    let GA := GeneralLinear (m 0 + 1) F.Carrier
    let Na := upperUnipotent (m 0 + 1) F.Carrier
    let Nb := upperUnipotent (m 1 + 1) F.Carrier
    let A0 := TwoBlockFirstBlockQuotient.normOneSubgroup F (m 0 + 1)
    let H := TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier
    let L := TwoBlockFirstBlockQuotient.mixedSubgroup F h
    let AQ := LeftUnipotentQuotient (m 0) F.Carrier
    let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier
    let LQ := TwoBlockFirstBlockQuotient.MixedQuotient F h
    letI : SecondCountableTopology GA := T.generalLinearSecondCountableTopology (m 0 + 1)
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace GA := borel GA
    letI : BorelSpace GA := ⟨rfl⟩
    letI : MeasurableSpace A0 := borel A0
    letI : BorelSpace A0 := ⟨rfl⟩
    letI : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    letI : MeasurableSpace H := borel H
    letI : BorelSpace H := ⟨rfl⟩
    letI : MeasurableSpace L := borel L
    letI : BorelSpace L := ⟨rfl⟩
    letI : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
      fun i => borel (upperUnipotent (m i + 1) F.Carrier)
    letI : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) :=
      fun _ => ⟨rfl⟩
    letI : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
      fun i => by
        let := T.generalLinearSecondCountableTopology (m i + 1)
        exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    -- These Borel instances use the actual finite product measurable spaces.
    letI : BorelSpace (TwoBlockUnipotentQuotient.BlockUnipotents m F.Carrier) := inferInstance
    letI : BorelSpace (A0 × Nb) := inferInstance
    letI : MeasurableSpace AQ := borel AQ
    letI : BorelSpace AQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace LQ := borel LQ
    letI : BorelSpace LQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μGA : Measure GA := generalLinearHaar F.Carrier (m 0)
    let μNa : Measure Na := unipotentHaar F.Carrier (m 0)
    let μNb : Measure Nb := unipotentHaar F.Carrier (m 1)
    let μH : Measure H := Measure.map (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F.Carrier)
      (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i)))
    μH.IsHaarMeasure ∧ μH.Regular ∧
      ∃ μA0 : Measure A0, μA0.IsHaarMeasure ∧ μA0.Regular ∧
        Measure.map Subtype.val μA0 = μGA.restrict (A0 : Set GA) ∧
        let μL : Measure L :=
          Measure.map (TwoBlockFirstBlockQuotient.mixedSubgroupEquiv F h) (μA0.prod μNb)
        μL.IsHaarMeasure ∧ μL.Regular ∧
          ∃ (hNa : Measure.IsMulRightInvariant μNa) (hH : Measure.IsMulRightInvariant μH)
            (hL : Measure.IsMulRightInvariant μL),
            letI := hNa
            letI := hH
            letI := hL
            (∃ νA : Measure AQ, IsCompatible Na μGA μNa νA) ∧
            (∃ νH : Measure HQ, IsCompatible H μG μH νH) ∧
            (∃ νL : Measure LQ, IsCompatible L μG μL νL) ∧
            ∀ (νA : Measure AQ) (νH : Measure HQ) (νL : Measure LQ)
              (hA : IsCompatible Na μGA μNa νA),
              IsCompatible H μG μH νH → IsCompatible L μG μL νL →
              SigmaFinite νA ∧ SigmaFinite νH ∧ SigmaFinite νL ∧
              ∀ k : ℤ,
                let hInvariant :=
                  TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
                    μGA μNa νA hA
                let νL0 := νL.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)
                let νHk := νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k)
                ∃ (κ : ProbabilityTheory.Kernel LQ HQ)
                  (_hκ : ProbabilityTheory.IsSFiniteKernel κ),
                  (∀ g : G, κ (Quotient.mk _ g) =
                    Measure.map (fun q => TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier q g)
                      (νA.restrict (RankinSelberg.determinantSlice T (m 0) k))) ∧
                  (κ ∘ₘ νL0 = νHk) ∧
                  (∀ f : HQ → ℝ≥0∞, Measurable f →
                    (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νL0) = ∫⁻ z, f z ∂νHk) ∧
                  (∀ f : HQ → ℂ, Measurable f →
                    (Integrable f νHk ↔
                      (∀ᵐ q ∂νL0, Integrable f (κ q)) ∧
                      Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νL0) ∧
                    (Integrable f νHk →
                      Integrable
                        (TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInvariant k f)
                        νL0 ∧
                      (∫ z, f z ∂νHk) =
                        ∫ q, TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInvariant k f q
                          ∂νL0))

end Langlands.RankinSelberg
