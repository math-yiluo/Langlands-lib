import Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement
import Langlands.Representation.RankinSelberg.TwoBlockFixedSliceAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof
import Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof

/-! # The actual fixed-slice first unfolding of JPSS Section 4.6 -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uV uW

/-- Absolute convergence and the normalized first unfolding on every determinant slice,
with the supplied self-dual rectangular measure and its integral-cube mass retained. -/
theorem twoBlockFixedSliceUnfolding :
    TwoBlockFixedSliceUnfoldingStatement.{uF,uV,uW} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν t m h
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  let G := GeneralLinear (t + 1) F.Carrier
  let N := upperUnipotent (t + 1) F.Carrier
  let H := blockUnipotent h F.Carrier
  let NQ := LeftUnipotentQuotient t F.Carrier
  let HQ := BlockQuotient h F.Carrier
  let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => borel (upperUnipotent (m i + 1) F.Carrier)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (BlockUnipotents m F.Carrier) := inferInstance
  let : BorelSpace R := inferInstance
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let μG : Measure G := generalLinearHaar F.Carrier t
  let μN : Measure N := unipotentHaar F.Carrier t
  let μH : Measure H := Measure.map (blockUnipotentEquiv h F.Carrier)
    (Measure.pi (fun i : Fin 2 => unipotentHaar F.Carrier (m i)))
  let μR : Measure R := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ (ValuativeRel.valuation F.Carrier).integer}
  obtain ⟨hμH, hμHreg, hN, hH, hexN, hexH, htower⟩ :=
    twoBlockUnipotentQuotientIntegration p F t m h
  let := hN
  let := hH
  obtain ⟨hc0, hc, κ, hκfin, hκ, htowerR⟩ := htower μR
  let := hκfin
  refine ⟨hc0, hc, hN, hH, hexN, hexH, ?_⟩
  intro W _ _ τ hτ ell
  obtain ⟨C, hC⟩ := TwoBlockConvergence.exists_bound_isAbsIntegrable_of_factorization
    F h ψ ν.val τ hτ ell (TwoBlockConvergence.exists_radical_factorization F h)
  refine ⟨C, ?_⟩
  intro u hu f V _ _ π hπ ℓ Wtest Φ k
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let E : HQ → ℂ := TwoBlockUnfolding.integrand ellu f Wtest.val Φ
  let slice : Set NQ := RankinSelberg.determinantSlice T t k
  let Hslice : Set HQ := projection h F.Carrier ⁻¹' slice
  let A : NQ → ℂ := radicalAverage F h μR E
  let Aabs : NQ → ℂ := radicalAverage F h μR (fun z => (‖E z‖ : ℂ))
  have hW : Continuous Wtest.val.val :=
    glModelFunction_continuous ψ t π hπ ℓ Wtest
  have hEc : Continuous E := TwoBlockUnfolding.integrand_continuous ψ ellu f Wtest.val Φ hW
  obtain ⟨hAc, hAabsc⟩ :=
    TwoBlockUnfolding.radicalAverages_continuous ψ ellu f Wtest.val Φ μR hW
  have hfiber : ∀ g : G, Integrable (fun x => E (fiberPoint h F.Carrier x g)) μR := by
    intro g
    have hraw := hC u hu f g
    change Integrable (TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g) μR at hraw
    simpa only [E, ellu, TwoBlockUnfolding.integrand_fiberPoint,
      twoBlockOppositeTwistFunctional_val] using
      (hraw.const_mul (Wtest.val.val g)).mul_const (Φ (lastRow g))
  refine ⟨hEc.measurable, hAc.measurable, hAabsc.measurable, hfiber, ?_, ?_⟩
  · intro g
    exact TwoBlockUnfolding.radicalAverage_integrand_mk ellu f Wtest.val Φ μR g
  · intro νN νH hνN hνH
    let := hνN.regular
    let := leftQuotient_locallyCompactSpace N
    let := Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap N)
    have hslice : IsClopen slice := RankinSelberg.isClopen_determinantSlice T t k
    have hrow := whittakerRowSliceCompactSupport F T t ψ V π hπ ℓ Wtest Φ k
    have habs_zero : ∀ q : NQ,
        whittakerNorm ψ Wtest.val q * ‖Φ (quotientLastRow t q)‖ = 0 → Aabs q = 0 := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        intro hz
        simp only [whittakerNorm_mk, quotientLastRow_mk] at hz
        change radicalAverage F h μR
          (fun z => (‖TwoBlockUnfolding.integrand ellu f Wtest.val Φ z‖ : ℂ))
          (Quotient.mk _ g) = 0
        rw [TwoBlockUnfolding.radicalAverage_norm_integrand_mk]
        rcases mul_eq_zero.mp hz with hw | hphi
        · simp only [hw, Complex.ofReal_zero, zero_mul]
        · simp only [hphi, Complex.ofReal_zero, mul_zero]
    have hcompact : HasCompactSupport (slice.indicator Aabs) := by
      apply hrow.mono
      intro q hq
      change slice.indicator Aabs q ≠ 0 at hq
      change slice.indicator
        (fun q => whittakerNorm ψ Wtest.val q * ‖Φ (quotientLastRow t q)‖) q ≠ 0
      intro hz
      by_cases hqs : q ∈ slice
      · rw [Set.indicator_of_mem hqs] at hq hz
        exact hq (habs_zero q hz)
      · simp only [Set.indicator_of_notMem hqs] at hq
        exact hq rfl
    have hAabsi : Integrable Aabs (νN.restrict slice) := by
      apply (integrable_indicator_iff hslice.isOpen.measurableSet).mp
      exact (hslice.continuous_indicator hAabsc).integrable_of_hasCompactSupport hcompact
    have hκfiber : ∀ q : NQ, Integrable E (κ q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [hκ g]
        have hcont : Continuous (fun x : R => fiberPoint h F.Carrier x g) :=
          continuous_quotient_mk'.comp
            ((TwoBlockJacquet.continuous_upperRadical h F.Carrier).mul continuous_const)
        exact (integrable_map_measure hEc.aestronglyMeasurable
          hcont.measurable.aemeasurable).mpr (hfiber g)
    have habs_eq : Aabs = fun q => Complex.ofReal (∫ z, ‖E z‖ ∂κ q) := by
      simpa only [integral_complex_ofReal] using
        radicalAverage_eq_integral_kernel F h μR κ hκ
          (fun z => (‖E z‖ : ℂ)) (Complex.measurable_ofReal.comp hEc.measurable.norm)
    have hnorm : Integrable (fun q => ∫ z, ‖E z‖ ∂κ q) (νN.restrict slice) := by
      have hr := hAabsi.re
      change Integrable (fun q => (Aabs q).re) (νN.restrict slice) at hr
      rw [habs_eq] at hr
      exact hr
    obtain ⟨_, _, ht⟩ := htowerR νN νH hνN hνH
    have htE := (ht slice hslice.isOpen.measurableSet).2.2 E hEc.measurable
    have hEi : Integrable E (νH.restrict Hslice) :=
      htE.1.mpr ⟨Filter.Eventually.of_forall hκfiber, hnorm⟩
    obtain ⟨hAi, hidentity⟩ := htE.2 hEi
    exact ⟨hEi, hAabsi, hAi, hidentity⟩

end Langlands.RankinSelberg
