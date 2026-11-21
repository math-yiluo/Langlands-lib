import Langlands.Analysis.Local.QuotientFinTwoCompatibility

/-! Coordinatewise transport of a two-factor subgroup Haar measure. -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory Topology

universe u v

variable {G : Fin 2 → Type u} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)]

local instance finTwoTransportSubgroupSecondCountable {K : Type*} [Group K]
    [TopologicalSpace K] [SecondCountableTopology K] (H : Subgroup K) :
    SecondCountableTopology H :=
  IsEmbedding.subtypeVal.secondCountableTopology

private def finTwoSubgroupCoordinates (A : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ A) ≃ₜ A 0 × A 1 :=
  (piSubgroupHomeomorph A).toHomeomorph.trans (Homeomorph.piFinTwo _)

variable [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SecondCountableTopology (G i)]

omit [∀ i, IsTopologicalGroup (G i)] in
private theorem finTwoSubgroupMeasure_eq_map_coordinates (A : ∀ i, Subgroup (G i))
    (μ₀ : Measure (A 0)) (μ₁ : Measure (A 1)) :
    finTwoSubgroupMeasure A μ₀ μ₁ = Measure.map (finTwoSubgroupCoordinates A).symm (μ₀.prod μ₁) := by
  unfold finTwoSubgroupMeasure prodSubgroupMeasure
  have hmeas : Measurable (⇑(prodSubgroupHomeomorph (A 0) (A 1)).symm) :=
    (prodSubgroupHomeomorph (A 0) (A 1)).symm.continuous.measurable
  rw [Measure.map_map (by fun_prop) hmeas]
  congr 1
  funext x
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

variable {G' : Fin 2 → Type v} [∀ i, Group (G' i)] [∀ i, TopologicalSpace (G' i)]
  [∀ i, IsTopologicalGroup (G' i)]
  [∀ i, MeasurableSpace (G' i)] [∀ i, BorelSpace (G' i)]
  [∀ i, SecondCountableTopology (G' i)]

omit [∀ i, IsTopologicalGroup (G i)] [∀ i, IsTopologicalGroup (G' i)] in
/-- Transport along the coordinatewise subgroup isomorphism gives the product
of the two transported Haar measures. -/
theorem map_finTwoSubgroupMeasure
    (A : ∀ i, Subgroup (G i)) (A' : ∀ i, Subgroup (G' i)) (e : ∀ i, A i ≃ₜ* A' i)
    (eA : (Subgroup.pi Set.univ A) ≃ₜ* (Subgroup.pi Set.univ A'))
    (he : ∀ x i, piSubgroupHomeomorph A' (eA x) i = e i (piSubgroupHomeomorph A x i))
    (μ₀ : Measure (A 0)) (μ₁ : Measure (A 1)) [SigmaFinite μ₀] [SigmaFinite μ₁] :
    Measure.map eA (finTwoSubgroupMeasure A μ₀ μ₁) =
      finTwoSubgroupMeasure A' (Measure.map (e 0) μ₀) (Measure.map (e 1) μ₁) := by
  let k := finTwoSubgroupCoordinates A
  let k' := finTwoSubgroupCoordinates A'
  have hm : Measurable (⇑eA) := eA.continuous.measurable
  have hm₀ : Measurable (⇑(e 0)) := (e 0).continuous.measurable
  have hm₁ : Measurable (⇑(e 1)) := (e 1).continuous.measurable
  rw [finTwoSubgroupMeasure_eq_map_coordinates, finTwoSubgroupMeasure_eq_map_coordinates,
    Measure.map_prod_map _ _ hm₀ hm₁]
  change Measure.map eA (Measure.map k.symm (μ₀.prod μ₁)) =
    Measure.map k'.symm (Measure.map (Prod.map (e 0) (e 1)) (μ₀.prod μ₁))
  rw [Measure.map_map hm k.symm.continuous.measurable,
    Measure.map_map k'.symm.continuous.measurable (hm₀.prodMap hm₁)]
  congr 1
  funext x
  apply k'.injective
  change k' (eA (k.symm x)) = k' (k'.symm (Prod.map (e 0) (e 1) x))
  rw [Homeomorph.apply_symm_apply]
  have h : k' (eA (k.symm x)) = Prod.map (e 0) (e 1) (k (k.symm x)) :=
    Prod.ext (he _ 0) (he _ 1)
  rw [h, Homeomorph.apply_symm_apply]

end Langlands.QuotientIntegration
