import Langlands.Analysis.Local.QuotientProductCompatibility

/-! Product-compatible quotient measures for a dependent product over `Fin 2`. -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Topology

universe u

variable {G : Fin 2 → Type u} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)]

private def finTwoProductEquiv : (∀ i, G i) ≃ₜ* G 0 × G 1 where
  toMulEquiv := { (Homeomorph.piFinTwo G).toEquiv with map_mul' := fun _ _ => rfl }
  continuous_toFun := (Homeomorph.piFinTwo G).continuous
  continuous_invFun := (Homeomorph.piFinTwo G).symm.continuous

variable (A : ∀ i, Subgroup (G i))

private def finTwoSubgroupEquiv : (Subgroup.pi Set.univ A) ≃ₜ* (A 0).prod (A 1) :=
  subgroupContinuousMulEquiv finTwoProductEquiv (Subgroup.pi Set.univ A) ((A 0).prod (A 1)) (by
    intro x
    change x 0 ∈ A 0 ∧ x 1 ∈ A 1 ↔ x ∈ Subgroup.pi Set.univ A
    rw [Subgroup.mem_pi]
    constructor
    · rintro ⟨h₀, h₁⟩ i -
      fin_cases i
      · exact h₀
      · exact h₁
    · intro hx
      exact ⟨hx 0 (Set.mem_univ _), hx 1 (Set.mem_univ _)⟩)

/-- View the left quotient by the two dependent subgroup factors as a product of quotients. -/
def finTwoLeftQuotientHomeomorph :
    LeftQuotient (Subgroup.pi Set.univ A) ≃ₜ LeftQuotient (A 0) × LeftQuotient (A 1) :=
  (leftQuotientPiHomeomorph A).trans (Homeomorph.piFinTwo _)

@[simp] theorem finTwoLeftQuotientHomeomorph_mk (x : ∀ i, G i) :
    finTwoLeftQuotientHomeomorph A (leftQuotientMap (Subgroup.pi Set.univ A) x) =
      (leftQuotientMap (A 0) (x 0), leftQuotientMap (A 1) (x 1)) := rfl

variable [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, SecondCountableTopology (G i)]

/-- Product subgroup Haar, transported to the subgroup of the dependent product. -/
def finTwoSubgroupMeasure (μ₀ : Measure (A 0)) (μ₁ : Measure (A 1)) :
    Measure (Subgroup.pi Set.univ A) :=
  Measure.map (finTwoSubgroupEquiv A).symm (prodSubgroupMeasure (A 0) (A 1) μ₀ μ₁)

instance finTwoSubgroupMeasure_isHaar (μ₀ : Measure (A 0)) (μ₁ : Measure (A 1))
    [μ₀.IsHaarMeasure] [μ₁.IsHaarMeasure] [SigmaFinite μ₀] [SigmaFinite μ₁] :
    (finTwoSubgroupMeasure A μ₀ μ₁).IsHaarMeasure :=
  (finTwoSubgroupEquiv A).symm.isHaarMeasure_map _

instance finTwoSubgroupMeasure_rightInvariant (μ₀ : Measure (A 0)) (μ₁ : Measure (A 1))
    [μ₀.IsMulRightInvariant] [μ₁.IsMulRightInvariant] [SigmaFinite μ₀] [SigmaFinite μ₁] :
    (finTwoSubgroupMeasure A μ₀ μ₁).IsMulRightInvariant :=
  isMulRightInvariant_map (finTwoSubgroupEquiv A).symm _

variable [MeasurableSpace (LeftQuotient (A 0))] [BorelSpace (LeftQuotient (A 0))]
  [MeasurableSpace (LeftQuotient (A 1))] [BorelSpace (LeftQuotient (A 1))]
  [MeasurableSpace (LeftQuotient (Subgroup.pi Set.univ A))]
  [BorelSpace (LeftQuotient (Subgroup.pi Set.univ A))]

/-- Product quotient measure in the dependent product coordinates. -/
def finTwoQuotientMeasure (ν₀ : Measure (LeftQuotient (A 0)))
    (ν₁ : Measure (LeftQuotient (A 1))) : Measure (LeftQuotient (Subgroup.pi Set.univ A)) :=
  Measure.map (finTwoLeftQuotientHomeomorph A).symm (ν₀.prod ν₁)

set_option maxHeartbeats 1000000 in
/-- Transport exact two-factor compatibility to the dependent product group and quotient. -/
theorem finTwoQuotientMeasure_isCompatible
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    [MeasurableSpace (LeftQuotient ((A 0).prod (A 1)))]
    [BorelSpace (LeftQuotient ((A 0).prod (A 1)))]
    (hA : ∀ i, IsClosed (A i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    [∀ i, SigmaFinite (μ i)]
    (μ₀ : Measure (A 0)) (μ₁ : Measure (A 1)) [μ₀.IsHaarMeasure] [μ₁.IsHaarMeasure]
    [μ₀.IsMulRightInvariant] [μ₁.IsMulRightInvariant] [SigmaFinite μ₀] [SigmaFinite μ₁]
    (ν₀ : Measure (LeftQuotient (A 0))) (ν₁ : Measure (LeftQuotient (A 1)))
    (hν₀ : IsCompatible (A 0) (μ 0) μ₀ ν₀) (hν₁ : IsCompatible (A 1) (μ 1) μ₁ ν₁) :
    IsCompatible (Subgroup.pi Set.univ A) (Measure.pi μ) (finTwoSubgroupMeasure A μ₀ μ₁)
      (finTwoQuotientMeasure A ν₀ ν₁) := by
  let : SecondCountableTopology (LeftQuotient (A 0)) :=
    (leftQuotient_isOpenQuotientMap (A 0)).secondCountableTopology
  let : SecondCountableTopology (LeftQuotient (A 1)) :=
    (leftQuotient_isOpenQuotientMap (A 1)).secondCountableTopology
  let e : (∀ i, G i) ≃ₜ* G 0 × G 1 := finTwoProductEquiv
  let eA := finTwoSubgroupEquiv A
  let eP := leftQuotientProdHomeomorph (A 0) (A 1)
  let eQ := eP.trans (finTwoLeftQuotientHomeomorph A).symm
  have heA (a : (A 0).prod (A 1)) : (eA.symm a).val = e.symm a.val := rfl
  have heQ (x : G 0 × G 1) : eQ (Quotient.mk _ x) = Quotient.mk _ (e.symm x) := by
    apply (finTwoLeftQuotientHomeomorph A).injective
    change (finTwoLeftQuotientHomeomorph A) ((finTwoLeftQuotientHomeomorph A).symm (eP ⟦x⟧)) = _
    rw [Homeomorph.apply_symm_apply]
    change eP ⟦x⟧ = (finTwoLeftQuotientHomeomorph A) (leftQuotientMap (Subgroup.pi Set.univ A) (e.symm x))
    rw [finTwoLeftQuotientHomeomorph_mk]
    exact (congrArg (Prod.map (leftQuotientMap (A 0)) (leftQuotientMap (A 1))) (e.apply_symm_apply x)).symm
  have hμ : Measure.map e.symm ((μ 0).prod (μ 1)) = Measure.pi μ :=
    (measurePreserving_piFinTwo μ).symm.map_eq
  have hν : Measure.map eQ (prodQuotientMeasure (A 0) (A 1) ν₀ ν₁) =
      finTwoQuotientMeasure A ν₀ ν₁ := by
    unfold prodQuotientMeasure finTwoQuotientMeasure
    rw [Measure.map_map eQ.continuous.measurable eP.symm.continuous.measurable]
    congr 1
    funext x
    change (finTwoLeftQuotientHomeomorph A).symm (eP (eP.symm x)) = _
    rw [Homeomorph.apply_symm_apply]
  have hprod := prodQuotientMeasure_isCompatible (A 0) (A 1) (hA 0) (hA 1)
    (μ 0) (μ 1) μ₀ μ₁ ν₀ ν₁ hν₀ hν₁
  have ht := isCompatible_map_equiv e.symm ((A 0).prod (A 1)) (Subgroup.pi Set.univ A)
    eA.symm heA eQ heQ ((μ 0).prod (μ 1)) _ _ hprod
  rw [hμ, hν] at ht
  exact ht

end Langlands.QuotientIntegration
