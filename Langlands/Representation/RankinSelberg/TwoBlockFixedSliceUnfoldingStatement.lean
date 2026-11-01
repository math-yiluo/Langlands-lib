import Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement

/-!
# Fixed-slice absolute convergence and the first Section 4.6 unfolding

JPSS (1983), Section 4.6, printed pages 411-412. For two blocks of full standard
Whittaker type, twisted by `|det|^(-u)` and `|det|^u`, the source substitutes the Jacquet
integral (4.6.2) into the outer integral (4) over `N_r \ G_r^m` and unfolds it to the
integral of `W(g) f[g; e, e] Φ(η g)` over `N_(t_1,t_2) \ G_r^m`, justified by the compact
support of `W(g) Φ(η g)` on `G_r^m` modulo `N_r`.

This module states, for every real `u` above one bound depending on the block data, the
measurability, fiber and fixed-slice absolute integrability, and the normalized restricted
Bochner identity for the published integrand on the actual quotient
`N_(t_1,t_2) \ GL_(t+1)`, together with the representative formula for its radical average.
The test representation is every smooth representation with an actual coefficient image,
which is a derived strengthening of the source's Whittaker-type test representation. This
is a proposition definition; no proof is supplied.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uV uW

/-- JPSS (1983), Section 4.6, printed pages 411-412, fixed-slice form. The rectangular
integral-cube mass `c` of the supplied self-dual product measure is positive and finite,
the right-invariance certificates hold and compatible quotient measures on `N \ G` and
`H \ G` exist. For blocks `τ` of full standard Whittaker type and every pair of supplied
inverse-character functionals `ℓ`, there is a real bound `C` such that for every `u > C`,
every section `f` of the actual lower induction of `(τ_0 |det|^(-u), τ_1 |det|^u)`, every
actual coefficient image `W` of a smooth test representation, every row Schwartz–Bruhat
function `Φ` and every integer `k`, the published integrand `E` on `H \ G` and its radical
averages are measurable, every rectangular fiber of `E` is integrable, the radical average
of `E` at `[g]` is `W(g) J(f)(g) Φ(lastRow g)`, and for every compatible pair of quotient
measures `E` is integrable on the determinant-`k` slice of `H \ G`, its absolute and signed
radical averages are integrable on the determinant-`k` slice of `N \ G`, and the restricted
integral of the radical average is `c` times the restricted integral of `E`. -/
def TwoBlockFixedSliceUnfoldingStatement : Prop :=
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
    let μR : Measure R := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
    let O := (ValuativeRel.valuation F.Carrier).integer
    let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ O}
    0 < c ∧ c < ⊤ ∧
      ∃ (hN : Measure.IsMulRightInvariant μN) (hH : Measure.IsMulRightInvariant μH),
        letI := hN
        letI := hH
        (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
        (∃ νH : Measure HQ, IsCompatible H μG μH νH) ∧
        ∀ {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
          (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
          (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
          ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i),
          ∃ C : ℝ, ∀ u : ℝ, C < u →
            ∀ (f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u))
              (V : Type uV) [AddCommGroup V] [Module ℂ V]
              (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V),
              IsSmooth π →
              ∀ (ℓ : glFunctionals ψ t π) (Wtest : (coefficientModel π ℓ).toSubmodule)
                (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)) (k : ℤ),
                let E : HQ → ℂ := TwoBlockUnfolding.integrand
                  (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)) f Wtest.val Φ
                let slice : Set NQ := RankinSelberg.determinantSlice T t k
                let Hslice : Set HQ := projection h F.Carrier ⁻¹' slice
                let A : NQ → ℂ := radicalAverage F h μR E
                let Aabs : NQ → ℂ := radicalAverage F h μR (fun z => (‖E z‖ : ℂ))
                Measurable E ∧ Measurable A ∧ Measurable Aabs ∧
                (∀ g : G, Integrable (fun x => E (fiberPoint h F.Carrier x g)) μR) ∧
                (∀ g : G, A (Quotient.mk _ g) =
                  Wtest.val.val g *
                    TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g *
                      Φ (lastRow g)) ∧
                ∀ (νN : Measure NQ) (νH : Measure HQ),
                  IsCompatible N μG μN νN → IsCompatible H μG μH νH →
                  Integrable E (νH.restrict Hslice) ∧
                  Integrable Aabs (νN.restrict slice) ∧
                  Integrable A (νN.restrict slice) ∧
                  (∫ q, A q ∂νN.restrict slice) = c.toReal • (∫ z, E z ∂νH.restrict Hslice)

end Langlands.RankinSelberg
