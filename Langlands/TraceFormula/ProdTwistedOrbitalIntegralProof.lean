import Langlands.Analysis.Local.QuotientCompatibleScaling
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.TraceFormula.ProductTwistedOrbitalStatement
import Langlands.TraceFormula.TwistedOrbitalProduct

/-! # Two-factor twisted orbital integrals with supplied compatible measures -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory Topology
open Langlands.QuotientIntegration

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- The twisted orbit function of a binary tensor is integrable and its integral factors. -/
theorem prodTwistedOrbitalIntegral : ProdTwistedOrbitalIntegralStatement.{u} := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    μ₁ _ μ₂ _ θ₁ θ₂ θ hθ₁ hθ₂ hθ δ₁ δ₂ m₁ b₁ m₂ b₂ _ _
    μC₁ right₁ finite₁ _ μC₂ right₂ finite₂ _ μC _ _ _
    ν₁ ν₂ ν hc₁ hc₂ hc hnormalize f₁ f₂ _ _ hf₁ hf₂
  let C₁ := twistedCentralizer θ₁ δ₁
  let C₂ := twistedCentralizer θ₂ δ₂
  let C := twistedCentralizer θ (δ₁, δ₂)
  have hθprod : Continuous θ := by
    have heq : (θ : G₁ × G₂ → G₁ × G₂) = fun x => (θ₁ x.1, θ₂ x.2) := funext hθ
    rw [heq]
    exact (hθ₁.comp continuous_fst).prodMk (hθ₂.comp continuous_snd)
  have hC₁ : IsClosed (C₁ : Set G₁) := isClosed_twistedCentralizer θ₁ hθ₁ δ₁
  have hC₂ : IsClosed (C₂ : Set G₂) := isClosed_twistedCentralizer θ₂ hθ₂ δ₂
  have hC : IsClosed (C : Set (G₁ × G₂)) := isClosed_twistedCentralizer θ hθprod (δ₁, δ₂)
  let : LocallyCompactSpace C₁ := hC₁.locallyCompactSpace
  let : LocallyCompactSpace C₂ := hC₂.locallyCompactSpace
  let : SecondCountableTopology C₁ := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology C₂ := IsEmbedding.subtypeVal.secondCountableTopology
  let sigma₁ : SigmaFinite μC₁ := inferInstance
  let sigma₂ : SigmaFinite μC₂ := inferInstance
  let : LocallyCompactSpace (LeftQuotient C₁) := leftQuotient_locallyCompactSpace C₁
  let : LocallyCompactSpace (LeftQuotient C₂) := leftQuotient_locallyCompactSpace C₂
  let : SecondCountableTopology (LeftQuotient C₁) :=
    (leftQuotient_isOpenQuotientMap C₁).secondCountableTopology
  let : SecondCountableTopology (LeftQuotient C₂) :=
    (leftQuotient_isOpenQuotientMap C₂).secondCountableTopology
  let : ν₁.Regular := hc₁.regular
  let : ν₂.Regular := hc₂.regular
  let D := ContinuousMulEquiv.refl (G₁ × G₂)
  let A₁ := twistedCentralizer θ₁ (D.symm (δ₁, δ₂)).1
  let A₂ := twistedCentralizer θ₂ (D.symm (δ₁, δ₂)).2
  let : MeasurableSpace (LeftQuotient A₁) := m₁
  let : BorelSpace (LeftQuotient A₁) := b₁
  let : MeasurableSpace (LeftQuotient A₂) := m₂
  let : BorelSpace (LeftQuotient A₂) := b₂
  let : SecondCountableTopology (LeftQuotient A₁) :=
    (leftQuotient_isOpenQuotientMap A₁).secondCountableTopology
  let : SFinite (α := LeftQuotient A₁) ν₁ := (inferInstance : SFinite ν₁)
  let : SFinite (α := LeftQuotient A₂) ν₂ := (inferInstance : SFinite ν₂)
  have hintertwines : ∀ p, θ (D p) = D (θ₁ p.1, θ₂ p.2) := hθ
  let μC₀ := twistedCentralizerProductMeasure D θ₁ θ₂ θ hintertwines (δ₁, δ₂) μC₁ μC₂
  let ν₀ := twistedOrbitProductMeasure D θ₁ θ₂ θ hintertwines (δ₁, δ₂) ν₁ ν₂
  have hμmap : μC₀.map (Subtype.val : C → G₁ × G₂) =
      (μC₁.map Subtype.val).prod (μC₂.map Subtype.val) := by
    let e := twistedCentralizerProductEquiv D θ₁ θ₂ θ hintertwines (δ₁, δ₂)
    let p := (prodSubgroupHomeomorph C₁ C₂).symm
    have he : Measurable (e : (C₁.prod C₂) → C) := e.continuous.measurable
    have hp : Measurable (p : C₁ × C₂ → (C₁.prod C₂)) := p.continuous.measurable
    change (Measure.map (e : (C₁.prod C₂) → C) (Measure.map p (μC₁.prod μC₂))).map Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe he,
      Measure.map_map (measurable_subtype_coe.comp he) hp,
      Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe]
    rfl
  have hμeq : μC₀ = μC :=
    hC.isClosedEmbedding_subtypeVal.measurableEmbedding.map_injective (hμmap.trans hnormalize.symm)
  subst μC
  have hν₀ : IsCompatible C (μ₁.prod μ₂) μC₀ ν₀ := by
    have hcompat := @twistedOrbitProductMeasure_isCompatible G₁ G₂ (G₁ × G₂) _ _ _ _ _ _
      D θ₁ θ₂ θ hintertwines (δ₁, δ₂) _ _ _ _ _ _ _ _ _ _ _ _ _ _
      μ₁ μ₂ μC₁ μC₂ sigma₁ sigma₂ right₁ right₂ _ _ finite₁ finite₂
      m₁ b₁ m₂ b₂ _ _ ν₁ ν₂ hC₁ hC₂ hc₁ hc₂
    change IsCompatible C ((μ₁.prod μ₂).map id) μC₀ ν₀ at hcompat
    simpa only [Measure.map_id] using hcompat
  rw [hc.unique hC hν₀]
  refine ⟨?_, twistedOrbitalIntegral_product D θ₁ θ₂ θ hintertwines (δ₁, δ₂) ν₁ ν₂ f₁ f₂⟩
  let e := twistedOrbitProductHomeomorph D θ₁ θ₂ θ hintertwines (δ₁, δ₂)
  change Integrable (twistedOrbitFunction θ (δ₁, δ₂) (fun x => f₁ x.1 * f₂ x.2))
    (Measure.map e.toMeasurableEquiv (ν₁.prod ν₂))
  apply (integrable_map_equiv e.toMeasurableEquiv _).2
  have horbit : (fun p => twistedOrbitFunction θ (δ₁, δ₂) (fun x => f₁ x.1 * f₂ x.2) (e p)) =
      (fun p : LeftQuotient C₁ × LeftQuotient C₂ =>
        twistedOrbitFunction θ₁ δ₁ f₁ p.1 * twistedOrbitFunction θ₂ δ₂ f₂ p.2) := by
    funext p
    rcases p with ⟨q, r⟩
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        rw [show e (Quotient.mk _ x, Quotient.mk _ y) = Quotient.mk _ (x, y) from
          twistedOrbitProductHomeomorph_mk D θ₁ θ₂ θ hintertwines (δ₁, δ₂) (x, y)]
        simp only [twistedOrbitFunction_mk, hθ]
        rfl
  change Integrable (fun p => twistedOrbitFunction θ (δ₁, δ₂)
    (fun x => f₁ x.1 * f₂ x.2) (e p)) (ν₁.prod ν₂)
  rw [horbit]
  exact hf₁.mul_prod hf₂

end Langlands.TraceFormula
