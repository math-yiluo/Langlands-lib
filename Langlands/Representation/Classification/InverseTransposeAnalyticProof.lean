import Langlands.Representation.Classification.InverseTransposeAnalyticStatement
import Langlands.Representation.MatrixCoefficient.GroupTransport
import Langlands.Representation.CompactCoefficient.GroupTransport
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Analytic inverse-transpose transport

Change variables on the actual quotient by the center and apply the original
analytic predicate to the pushed-forward Haar measure.
-/

noncomputable section

namespace Langlands

universe uG uH uV uF

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  [MeasurableSpace (H ⧸ Subgroup.center H)] [BorelSpace (H ⧸ Subgroup.center H)]

/-- Tempered coefficient bounds pull back after pushing the Haar measure forward. -/
theorem isTemperedModCenter_comp_continuousMulEquiv
    (ρ : Representation ℂ G V) (e : H ≃ₜ* G)
    (μ : MeasureTheory.Measure (H ⧸ Subgroup.center H)) [μ.IsHaarMeasure]
    (hρ : IsTemperedModCenter ρ (μ.map (centralQuotientCongr e))) :
    IsTemperedModCenter (ρ.comp e.toMonoidHom) μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨isAdmissible_comp_continuousMulEquiv ρ e hρ,
    c.compContinuousMulEquiv e, ?_⟩
  intro ℓ v ε hε
  rw [c.coefficientNorm_compContinuousMulEquiv]
  exact (hc ⟨ℓ, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ).mp
    ℓ.property⟩ v ε hε).comp_of_map
      (centralQuotientCongr e).continuous.measurable.aemeasurable

/-- Square-integrable coefficient bounds use the same change of variables. -/
theorem isSquareIntegrableModCenter_comp_continuousMulEquiv
    (ρ : Representation ℂ G V) (e : H ≃ₜ* G)
    (μ : MeasureTheory.Measure (H ⧸ Subgroup.center H)) [μ.IsHaarMeasure]
    (hρ : IsSquareIntegrableModCenter ρ (μ.map (centralQuotientCongr e))) :
    IsSquareIntegrableModCenter (ρ.comp e.toMonoidHom) μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨isAdmissible_comp_continuousMulEquiv ρ e hρ,
    c.compContinuousMulEquiv e, ?_⟩
  intro ℓ v
  rw [c.coefficientNorm_compContinuousMulEquiv]
  exact (hc ⟨ℓ, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ).mp
    ℓ.property⟩ v).comp_of_map
      (centralQuotientCongr e).continuous.measurable.aemeasurable

end Generic

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- All-Haar temperedness pulls back through any continuous group automorphism. -/
theorem isTempered_comp_continuousMulEquiv
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (e : letI := T.topology
      GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier)
    (hρ : T.IsTempered ρ) : T.IsTempered (ρ.comp e.toMonoidHom) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro μ hμ
  exact isTemperedModCenter_comp_continuousMulEquiv ρ e μ (hρ _)

/-- All-Haar square-integrability pulls back through a continuous automorphism. -/
theorem isSquareIntegrable_comp_continuousMulEquiv
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (e : letI := T.topology
      GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier)
    (hρ : T.IsSquareIntegrable ρ) :
    T.IsSquareIntegrable (ρ.comp e.toMonoidHom) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro μ hμ
  exact isSquareIntegrableModCenter_comp_continuousMulEquiv ρ e μ (hρ _)

end PadicField.TopologicalData

namespace Classification

/-- Both analytic predicates are preserved and reflected by inverse transpose. -/
theorem padicInverseTransposeAnalytic.{uField, uCarrier} :
    PadicInverseTransposeAnalyticStatement.{uField, uCarrier} := by
  intro p _ F T
  have hinv {n : ℕ} {V : Type uCarrier} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
      (ρ.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom).comp
          (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom = ρ := by
    ext g v
    change ρ (GeneralLinear.inverseTranspose n F.Carrier
      (GeneralLinear.inverseTranspose n F.Carrier g)) v = ρ g v
    rw [GeneralLinear.inverseTranspose_involutive]
  constructor
  · intro n _ V _ _ ρ
    constructor
    · intro hρ
      have h := T.isTempered_comp_continuousMulEquiv _
        (T.generalLinearInverseTranspose n) hρ
      change T.IsTempered
        ((ρ.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom).comp
          (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom) at h
      rwa [hinv] at h
    · exact T.isTempered_comp_continuousMulEquiv ρ (T.generalLinearInverseTranspose n)
  · intro n _ V _ _ ρ
    constructor
    · intro hρ
      have h := T.isSquareIntegrable_comp_continuousMulEquiv _
        (T.generalLinearInverseTranspose n) hρ
      change T.IsSquareIntegrable
        ((ρ.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom).comp
          (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom) at h
      rwa [hinv] at h
    · exact T.isSquareIntegrable_comp_continuousMulEquiv ρ
        (T.generalLinearInverseTranspose n)

end Classification
end Langlands
