import Langlands.BaseChange.NormCentralizer
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters

/-! Transport of associated measures by the centralizer equivalence at an exact norm. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.TraceFormula

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type v} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  {n l : ℕ} {σ : E ≃ₐ[F] E} {δ : GeneralLinear n E} {γ : GeneralLinear n F}

/-- The centralizer isomorphism at an exact regular norm is coefficient extension. -/
def exactNormCentralizerEquiv (hσ : IsCyclicAlgebra σ l) (hγ : IsRegularSemisimple γ)
    (hn : cyclicNorm σ l δ = baseChange F E n γ) : glCentralizer γ ≃ₜ* sigmaCentralizer σ n δ :=
  normCentralizerEquiv hσ hγ 1 (by simpa only [inv_one, one_mul, mul_one] using hn)

@[simp] theorem exactNormCentralizerEquiv_apply_val
    (hσ : IsCyclicAlgebra σ l) (hγ : IsRegularSemisimple γ)
    (hn : cyclicNorm σ l δ = baseChange F E n γ) (t : glCentralizer γ) :
    (exactNormCentralizerEquiv hσ hγ hn t).val = baseChange F E n t.val := by
  rw [exactNormCentralizerEquiv, normCentralizerEquiv_apply_val, inv_one, one_mul, mul_one]

variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
variable [T2Space (GeneralLinear n E)]

/-- At an exact regular norm, association of measures is precisely transport by the
centralizer isomorphism, even when the association uses another norm conjugator. -/
theorem isAssociatedMeasure_iff_map_exactNormCentralizerEquiv
    (hσ : IsCyclicAlgebra σ l) (hγ : IsRegularSemisimple γ)
    (hn : cyclicNorm σ l δ = baseChange F E n γ)
    (μδ : Measure (sigmaCentralizer σ n δ)) (μγ : Measure (glCentralizer γ)) :
    IsAssociatedMeasure σ l δ γ μδ μγ ↔
      μδ = Measure.map (exactNormCentralizerEquiv hσ hγ hn) μγ := by
  let e := exactNormCentralizerEquiv hσ hγ hn
  have hOne : (1 : GeneralLinear n E)⁻¹ * cyclicNorm σ l δ * 1 = baseChange F E n γ := by
    simpa only [inv_one, one_mul, mul_one] using hn
  have hClosed := isClosed_twistedCentralizer (entrywiseAut σ n)
    (SigmaLiftCharacterIdentity.continuous_entrywiseAut σ) δ
  have hEmb : MeasurableEmbedding (Subtype.val : sigmaCentralizer σ n δ → GeneralLinear n E) :=
    MeasurableEmbedding.subtype_coe hClosed.measurableSet
  have he (t : glCentralizer γ) : (e t).val = baseChange F E n t.val :=
    exactNormCentralizerEquiv_apply_val hσ hγ hn t
  have heMeas : Measurable (⇑e) := e.continuous.measurable
  have hMap : Measure.map (Subtype.val : sigmaCentralizer σ n δ → GeneralLinear n E)
      (Measure.map e μγ) = Measure.map (fun t : glCentralizer γ => baseChange F E n t.val) μγ := by
    rw [Measure.map_map hEmb.measurable heMeas]
    congr 1
    exact funext he
  constructor
  · rintro ⟨x, hx, hμ⟩
    let : Module.Finite F E := hσ.1
    have hcomm (a b : GeneralLinear n E) (ha : Commute a (baseChange F E n γ))
        (hb : Commute b (baseChange F E n γ)) : Commute a b :=
      commute_of_commute_baseChange hγ ha hb
    have hx₀ (t : sigmaCentralizer σ n δ) : x⁻¹ * t.val * x = t.val := by
      simpa only [inv_one, one_mul, mul_one] using
        normConjugator_on_sigmaCentralizer hσ.pow_eq_one hcomm hx hOne t
    apply hEmb.map_injective
    rw [hMap]
    simpa only [hx₀] using hμ
  · intro hμ
    refine ⟨1, hOne, ?_⟩
    simpa only [inv_one, one_mul, mul_one, hμ] using hMap

end Langlands.BaseChange
