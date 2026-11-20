import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.BaseChange.NormCentralizer
import Langlands.BaseChange.OrbitalMeasureExistenceStatement
import Mathlib.Topology.Metrizable.Urysohn

/-! Existence of the centralizer and quotient measures used in orbital integral concordance. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix MeasureTheory Topology
open Langlands.JacquetLanglands Langlands.QuotientIntegration

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

private theorem exists_compatible_of_closed {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μG : Measure G) (μH : Measure H)
    [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] : CompatibleMeasureExists H μG μH := by
  let _ : LocallyCompactSpace H := hH.locallyCompactSpace
  let _ : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology ↥(H : Set G))
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : μH.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μH
  exact compatibleMeasureExists H hH μG μH

private theorem isClosed_glCentralizer {F : Type u} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] {n : ℕ} [T2Space (GeneralLinear n F)] (γ : GeneralLinear n F) :
    IsClosed (glCentralizer γ : Set (GeneralLinear n F)) := by
  rw [glCentralizer_eq_centralizer]
  exact Set.isClosed_centralizer _

private theorem isClosed_sigmaCentralizer {F : Type u} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] {n : ℕ} [T2Space (GeneralLinear n E)]
    (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) :
    IsClosed (sigmaCentralizer σ n δ : Set (GeneralLinear n E)) := by
  have hσ : Continuous (entrywiseAut σ n) :=
    (IsModuleTopology.continuous_of_linearMap σ.toLinearMap).generalLinearGroup_map
  change IsClosed {x : GeneralLinear n E | x⁻¹ * δ * entrywiseAut σ n x = δ}
  exact isClosed_eq ((continuous_inv.mul continuous_const).mul hσ) continuous_const

/-- The centralizer and quotient measures in regular semisimple orbital integral
concordance exist for the supplied ambient Haar measures. -/
theorem orbitalMeasureExistence : OrbitalMeasureExistenceStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _
  let _ : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let _ : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let _ : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let _ : Module.Finite F E := hσ.1
  let _ : IsReduced E := hσ.2.2.1
  let _ : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hE_sep, hE_compact, hE_countable⟩ := finiteAlgebraTopology F E
  let _ : T2Space E := hE_sep
  let _ : LocallyCompactSpace E := hE_compact
  let _ : SecondCountableTopology E := hE_countable
  let _ : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  let _ : SecondCountableTopology (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let _ : SecondCountableTopology (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let _ : SecondCountableTopology (GeneralLinear n E) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : μF.IsMulRightInvariant := generalLinear_haar_rightInvariant F n μF
  have : μE.IsMulRightInvariant := generalLinear_haar_rightInvariant E n μE
  constructor
  · intro γ hγ
    have hclosed := isClosed_glCentralizer γ
    constructor
    · let _ : LocallyCompactSpace (glCentralizer γ) := hclosed.locallyCompactSpace
      let μγ : Measure (glCentralizer γ) := Measure.haar
      have : μγ.IsHaarMeasure := inferInstance
      refine ⟨μγ, inferInstance, ⟨fun t => ?_⟩⟩
      have heq : (· * t) = (t * ·) := funext fun s => glCentralizer_mul_comm hγ s t
      rw [heq, map_mul_left_eq_self]
    · intro μγ _ _
      exact exists_compatible_of_closed (glCentralizer γ) hclosed μF μγ
  · intro δ γ hassoc hγ μγ _ _
    obtain ⟨x, hx⟩ := hassoc
    let e := normCentralizerEquiv hσ hγ x hx
    let μδ := Measure.map e μγ
    have : μδ.IsHaarMeasure := e.isHaarMeasure_map μγ
    have : μδ.IsMulRightInvariant := isMulRightInvariant_map e μγ
    refine ⟨μδ, inferInstance, inferInstance, ⟨x, hx, ?_⟩, ?_⟩
    · have hconj : Continuous (fun c : sigmaCentralizer σ n δ =>
          x⁻¹ * c.val * x) := (continuous_const.mul continuous_subtype_val).mul continuous_const
      have heMeas : Measurable (⇑e) := e.continuous.measurable
      change Measure.map _ (Measure.map e μγ) = _
      rw [Measure.map_map hconj.measurable heMeas]
      congr 1
      funext t
      change x⁻¹ * (e t).val * x = baseChange F E n t.val
      rw [normCentralizerEquiv_apply_val hσ hγ x hx t]
      group
    · exact exists_compatible_of_closed (sigmaCentralizer σ n δ)
        (isClosed_sigmaCentralizer σ δ) μE μδ

end Langlands.BaseChange
