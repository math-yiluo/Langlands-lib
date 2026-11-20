import Langlands.BaseChange.OrbitalIntegral
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped CompactlySupported NNReal

namespace Langlands.QuotientIntegration

/-- Scaling the subgroup Haar measure by `c` scales the compatible quotient measure
inversely, written without division so it can also be used for uniqueness. -/
theorem IsCompatible.eq_smul_of_subgroup_smul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (LeftQuotient H)]
    [BorelSpace (LeftQuotient H)]
    {μG : Measure G} {μ₁ μ₂ : Measure H} [μ₁.IsHaarMeasure] [μ₁.Regular]
    [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    {ν₁ ν₂ : Measure (LeftQuotient H)} (h₁ : IsCompatible H μG μ₁ ν₁)
    (h₂ : IsCompatible H μG μ₂ ν₂) {c : ℝ≥0} (hc : μ₂ = c • μ₁) :
    ν₁ = c • ν₂ := by
  let := leftQuotient_t2Space H hH
  let := leftQuotient_locallyCompactSpace H
  let : ν₁.Regular := h₁.regular
  let : ν₂.Regular := h₂.regular
  let : (c • ν₂).Regular := Measure.Regular.smul ENNReal.coe_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨f, hf, _⟩ := realQuotientPositiveLifting H hH μ₁ φ
  have havg₁ : quotientAverageReal H μ₁ f = φ := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have havg₂ : quotientAverageReal H μ₂ f = fun q => (c : ℝ) * φ q := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [quotientAverageReal_mk, hc, integral_smul_nnreal_measure, hf, NNReal.smul_def,
        smul_eq_mul]
  calc
    (∫ q, φ q ∂ν₁) = ∫ g, f g ∂μG := by
      rw [← h₁.integral_quotientAverageReal f f.continuous f.hasCompactSupport, havg₁]
    _ = ∫ q, φ q ∂(c • ν₂) := by
      rw [← h₂.integral_quotientAverageReal f f.continuous f.hasCompactSupport, havg₂,
        integral_const_mul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

end Langlands.QuotientIntegration

namespace Langlands.TraceFormula

variable {G : Type*} [Group G]
variable {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]

/-- A continuous twist has closed centralizers. -/
theorem isClosed_twistedCentralizer [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (θ : Θ) (hθ : Continuous (fun x : G => θ x)) (δ : G) :
    IsClosed (twistedCentralizer θ δ : Set G) :=
  isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const

/-- Rescaling the quotient measure rescales the actual twisted orbital integral. -/
theorem twistedOrbitalIntegral_smul_measure (θ : Θ) (δ : G)
    [MeasurableSpace (Langlands.QuotientIntegration.LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (Langlands.QuotientIntegration.LeftQuotient (twistedCentralizer θ δ)))
    (c : ℝ≥0) (f : G → ℂ) :
    twistedOrbitalIntegral θ δ (c • ν) f = (c : ℝ) • twistedOrbitalIntegral θ δ ν f :=
  integral_smul_nnreal_measure ..

end Langlands.TraceFormula

namespace Langlands.BaseChange

open Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

variable {F : Type*} [Field F] {E : Type*} [CommRing E] [Algebra F E] {n l : ℕ}
variable {σ : E ≃ₐ[F] E} {δ : GeneralLinear n E} {γ : GeneralLinear n F}

/-- Two norm conjugators act in the same way on the twisted centralizer
when the scalar-extended ordinary centralizer is commutative. -/
theorem normConjugator_on_sigmaCentralizer (hσ : σ ^ l = 1)
    (hcomm : ∀ a b : GeneralLinear n E, Commute a (baseChange F E n γ) →
      Commute b (baseChange F E n γ) → Commute a b)
    {x y : GeneralLinear n E}
    (hx : x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ)
    (hy : y⁻¹ * cyclicNorm σ l δ * y = baseChange F E n γ)
    (c : sigmaCentralizer σ n δ) :
    x⁻¹ * (c : GeneralLinear n E) * x = y⁻¹ * (c : GeneralLinear n E) * y := by
  have hN : (c : GeneralLinear n E)⁻¹ * cyclicNorm σ l δ * c = cyclicNorm σ l δ := by
    have h := congrArg (cyclicNorm σ l)
      ((mem_sigmaCentralizer σ n δ c).mp c.property)
    rwa [cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply] at h
  have hc : Commute (c : GeneralLinear n E) (cyclicNorm σ l δ) := by
    calc
      (c : GeneralLinear n E) * cyclicNorm σ l δ =
          c * ((c : GeneralLinear n E)⁻¹ * cyclicNorm σ l δ * c) := by rw [hN]
      _ = cyclicNorm σ l δ * c := by group
  have ha : Commute (x⁻¹ * (c : GeneralLinear n E) * x) (baseChange F E n γ) := by
    rw [← hx]
    calc
      (x⁻¹ * (c : GeneralLinear n E) * x) * (x⁻¹ * cyclicNorm σ l δ * x) =
          x⁻¹ * ((c : GeneralLinear n E) * cyclicNorm σ l δ) * x := by group
      _ = x⁻¹ * (cyclicNorm σ l δ * c) * x := by rw [hc.eq]
      _ = (x⁻¹ * cyclicNorm σ l δ * x) * (x⁻¹ * (c : GeneralLinear n E) * x) := by group
  have hb : Commute (x⁻¹ * y) (baseChange F E n γ) := by
    calc
      (x⁻¹ * y) * baseChange F E n γ = x⁻¹ * cyclicNorm σ l δ * y := by rw [← hy]; group
      _ = baseChange F E n γ * (x⁻¹ * y) := by rw [← hx]; group
  symm
  calc
    y⁻¹ * (c : GeneralLinear n E) * y =
        (x⁻¹ * y)⁻¹ * ((x⁻¹ * (c : GeneralLinear n E) * x) * (x⁻¹ * y)) := by group
    _ = x⁻¹ * (c : GeneralLinear n E) * x := by
      rw [(hcomm _ _ ha hb).eq, inv_mul_cancel_left]

variable [TopologicalSpace F] [IsTopologicalRing F] [TopologicalSpace E] [IsTopologicalRing E]
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
variable [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
variable [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]

/-- At a regular associated pair, an equality for one associated choice of measures
gives concordance for every associated choice. The topology and commutativity premises
state the properties used from the centralizer and the scalar-extension map. -/
theorem ConcordAt.of_associated_pair
    [SecondCountableTopology (GeneralLinear n F)] [SecondCountableTopology (GeneralLinear n E)]
    (hσ : σ ^ l = 1)
    (hθ : Continuous (fun x : GeneralLinear n E => entrywiseAut σ n x))
    (hcomm : ∀ a b : GeneralLinear n E, Commute a (baseChange F E n γ) →
      Commute b (baseChange F E n γ) → Commute a b)
    (hj : MeasurableEmbedding (fun t : glCentralizer γ => baseChange F E n t))
    {μF : Measure (GeneralLinear n F)} {μE : Measure (GeneralLinear n E)}
    {φ : GeneralLinear n E → ℂ} {f : GeneralLinear n F → ℂ}
    {μδ : Measure (sigmaCentralizer σ n δ)} [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
    {μγ : Measure (glCentralizer γ)} [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    {νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))}
    {νγ : Measure (LeftQuotient (glCentralizer γ))}
    (hδ : IsCompatible (sigmaCentralizer σ n δ) μE μδ νδ)
    (hγ : IsCompatible (glCentralizer γ) μF μγ νγ)
    (hassoc : IsAssociatedMeasure σ l δ γ μδ μγ)
    (heq : sigmaOrbitalIntegral σ n δ νδ φ = orbitalIntegral γ νγ f) :
    ConcordAt σ l μF μE φ f δ γ := by
  intro μδ' _ _ μγ' _ _ νδ' νγ' hδ' hγ' hassoc'
  have hcδ := isClosed_twistedCentralizer (entrywiseAut σ n) hθ δ
  have hcγ := isClosed_twistedCentralizer (MonoidHom.id _) continuous_id γ
  let : LocallyCompactSpace (sigmaCentralizer σ n δ) := hcδ.locallyCompactSpace
  let : LocallyCompactSpace (glCentralizer γ) := hcγ.locallyCompactSpace
  let : SecondCountableTopology (sigmaCentralizer σ n δ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology (glCentralizer γ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  let c := haarScalarFactor μδ' μδ
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure μδ' μδ
  have hδscale : μδ' = c • μδ := isMulLeftInvariant_eq_smul μδ' μδ
  obtain ⟨x, hx, hmap⟩ := hassoc
  obtain ⟨y, hy, hmap'⟩ := hassoc'
  let transport : sigmaCentralizer σ n δ → GeneralLinear n E :=
    fun z => x⁻¹ * (z : GeneralLinear n E) * x
  have htransport : Measurable transport :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hmap'₁ : Measure.map transport μδ' =
      Measure.map (fun t : glCentralizer γ => baseChange F E n t) μγ' := by
    rw [show transport = fun z : sigmaCentralizer σ n δ => y⁻¹ * (z : GeneralLinear n E) * y from
      funext (normConjugator_on_sigmaCentralizer hσ hcomm hx hy)]
    exact hmap'
  have hγscale : μγ' = c • μγ := by
    apply hj.map_injective
    rw [← hmap'₁, hδscale, Measure.map_smul _ htransport.aemeasurable,
      Measure.map_smul _ hj.measurable.aemeasurable]
    exact congrArg (c • ·) hmap
  have hvδ := hδ.eq_smul_of_subgroup_smul hcδ hδ' hδscale
  have hvγ := hγ.eq_smul_of_subgroup_smul hcγ hγ' hγscale
  rw [hvδ, hvγ, sigmaOrbitalIntegral, orbitalIntegral, twistedOrbitalIntegral_smul_measure,
    twistedOrbitalIntegral_smul_measure] at heq
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  exact smul_right_injective ℂ hc' heq

/-- A zero orbital integral for one Haar and compatible quotient pair remains
zero for every such pair on the same centralizer. -/
theorem orbitalIntegral_eq_zero_of_compatible
    [SecondCountableTopology (GeneralLinear n F)]
    {μF : Measure (GeneralLinear n F)} {f : GeneralLinear n F → ℂ}
    {μγ μγ' : Measure (glCentralizer γ)} [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    [μγ'.IsHaarMeasure] [μγ'.IsMulRightInvariant]
    {νγ νγ' : Measure (LeftQuotient (glCentralizer γ))}
    (hγ : IsCompatible (glCentralizer γ) μF μγ νγ)
    (hγ' : IsCompatible (glCentralizer γ) μF μγ' νγ')
    (hz : orbitalIntegral γ νγ f = 0) :
    orbitalIntegral γ νγ' f = 0 := by
  have hclosed := isClosed_twistedCentralizer (MonoidHom.id _) continuous_id γ
  let : LocallyCompactSpace (glCentralizer γ) := hclosed.locallyCompactSpace
  let : SecondCountableTopology (glCentralizer γ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  let c := haarScalarFactor μγ' μγ
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure μγ' μγ
  have hscale : μγ' = c • μγ := isMulLeftInvariant_eq_smul μγ' μγ
  rw [hγ.eq_smul_of_subgroup_smul hclosed hγ' hscale, orbitalIntegral,
    twistedOrbitalIntegral_smul_measure] at hz
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  exact (smul_eq_zero.mp hz).resolve_left hc'

end Langlands.BaseChange
