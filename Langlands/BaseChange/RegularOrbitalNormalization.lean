import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.RegularCentralizerCompact
import Langlands.BaseChange.RegularOrbitalProfiles

/-! Normalized centralizer and compatible quotient measures for regular orbital integrals. -/

noncomputable section

namespace Langlands.BaseChange

open Set MeasureTheory MeasureTheory.Measure _root_.Topology
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

namespace RegularOrbitalMeasures

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {θ : G →* G} {μ : Measure G} {R : Set G}

/-- Each centralizer Haar measure gives its largest compact open subgroup mass one. -/
def IsNormalized (m : RegularOrbitalMeasures θ μ R) : Prop :=
  ∀ r : R, ∃ h : HasLargestCompactOpenSubgroup (twistedCentralizer θ (r : G)),
    m.centralizer r = h.haar

/-- Choose normalized Haar and compatible quotient measures for commutative
centralizers with largest compact open subgroups. -/
theorem exists_isNormalized
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (hθ : Continuous θ)
    (hK : ∀ r : R, HasLargestCompactOpenSubgroup (twistedCentralizer θ (r : G)))
    (hcomm : ∀ (r : R) (s t : twistedCentralizer θ (r : G)), s * t = t * s) :
    ∃ m : RegularOrbitalMeasures θ μ R, m.IsNormalized := by
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hright (r : R) : (hK r).haar.IsMulRightInvariant := by
    refine ⟨fun t => ?_⟩
    have heq : (· * t) = (t * ·) := funext fun s => hcomm r s t
    rw [heq, map_mul_left_eq_self]
  have hν (r : R) : let _ := hright r
      CompatibleMeasureExists (twistedCentralizer θ (r : G)) μ (hK r).haar := by
    let := hright r
    exact compatibleMeasureExists _ (isClosed_twistedCentralizer θ hθ r) μ (hK r).haar
  exact ⟨{
    centralizer := fun r => (hK r).haar
    quotient := fun r => (hν r).choose
    haar := fun _ => inferInstance
    rightInvariant := hright
    compatible := fun r => (hν r).choose_spec },
    fun r => ⟨hK r, rfl⟩⟩

end RegularOrbitalMeasures

universe u v

/-- The regular centralizer normalizations give associated measure families. -/
def RegularOrbitalNormalizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
    ∃ (mF : RegularOrbitalMeasures (MonoidHom.id _) μF {γ | IsRegularSemisimple γ})
      (mE : RegularOrbitalMeasures (entrywiseAut σ n).toMonoidHom μE {δ | IsSigmaRegular σ l δ}),
      mF.IsNormalized ∧ mE.IsNormalized ∧
      ∀ (δ : {δ : GeneralLinear n E // IsSigmaRegular σ l δ})
        (γ : {γ : GeneralLinear n F // IsRegularSemisimple γ}),
        IsNormAssociated σ l (δ : GeneralLinear n E) γ →
        IsAssociatedMeasure σ l (δ : GeneralLinear n E) (γ : GeneralLinear n F)
          (mE.centralizer δ) (mF.centralizer γ)

theorem regularOrbitalNormalization : RegularOrbitalNormalizationStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _
  let : Module.Finite F E := hσ.1
  let : IsReduced E := hσ.2.2.1
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hE₂, hEc, _⟩ := finiteAlgebraTopology F E
  let : T2Space E := hE₂
  let : LocallyCompactSpace E := hEc
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) n
  let : μF.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μF
  let : μE.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μE
  let : μF.IsMulRightInvariant := generalLinear_haar_rightInvariant F n μF
  let : μE.IsMulRightInvariant := generalLinear_haar_rightInvariant E n μE
  obtain ⟨mF, hmF⟩ := RegularOrbitalMeasures.exists_isNormalized
    (θ := MonoidHom.id _) (μ := μF) (R := {γ | IsRegularSemisimple γ}) continuous_id
    (fun γ => regularCentralizer_hasLargestCompactOpenSubgroup F n γ γ.property)
    (fun γ => glCentralizer_mul_comm γ.property)
  have hθ : Continuous (entrywiseAut σ n).toMonoidHom := continuous_entrywiseAut σ n
  obtain ⟨mE, hmE⟩ := RegularOrbitalMeasures.exists_isNormalized
    (μ := μE) (R := {δ | IsSigmaRegular σ l δ}) hθ
    (fun δ => by
      obtain ⟨γ, hassoc, hγ⟩ := δ.property
      exact sigmaCentralizer_hasLargestCompactOpenSubgroup hσ hγ hassoc)
    (fun δ s t => by
      obtain ⟨γ, ⟨x, hx⟩, hγ⟩ := δ.property
      let e : glCentralizer γ ≃ₜ* twistedCentralizer (entrywiseAut σ n).toMonoidHom δ :=
        normCentralizerEquiv hσ hγ x hx
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact glCentralizer_mul_comm hγ _ _)
  refine ⟨mF, mE, hmF, hmE, ?_⟩
  intro δ γ hassoc
  obtain ⟨x, hx⟩ := hassoc
  obtain ⟨kF, hkF⟩ := hmF γ
  obtain ⟨kE, hkE⟩ := hmE δ
  change HasLargestCompactOpenSubgroup (sigmaCentralizer σ n δ) at kE
  let e := normCentralizerEquiv hσ γ.property x hx
  have hc := isClosed_twistedCentralizer (entrywiseAut σ n) hθ (δ : GeneralLinear n E)
  let : LocallyCompactSpace (sigmaCentralizer σ n δ) := hc.locallyCompactSpace
  let : SecondCountableTopology (sigmaCentralizer σ n δ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨x, hx, ?_⟩
  let conj : sigmaCentralizer σ n δ → GeneralLinear n E := fun c => x⁻¹ * c.val * x
  have hconj : Continuous conj :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  let μδ : Measure (sigmaCentralizer σ n δ) := mE.centralizer δ
  have hδ : μδ = Measure.map e kF.haar :=
    hkE.trans (kF.map_haar kE e).symm
  have he : Measurable (⇑e) := e.continuous.measurable
  change Measure.map conj μδ = Measure.map _ (mF.centralizer γ)
  rw [hδ, hkF, Measure.map_map hconj.measurable he]
  congr 1
  funext t
  change x⁻¹ * (e t).val * x = baseChange F E n t.val
  rw [normCentralizerEquiv_apply_val hσ γ.property x hx t]
  group

end Langlands.BaseChange
