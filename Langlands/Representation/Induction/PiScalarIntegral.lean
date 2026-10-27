import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Compact scalar averages on finite products

Right-translation invariance of compact averages of covariant locally constant
scalar functions passes from the factors of a finite product to the product,
with the product of the factor probability measures.
-/

noncomputable section

open MeasureTheory Function
open scoped NNReal

namespace Langlands.Induction

universe u v

section Update

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {X : ι → Type v}
  [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling one coordinate of a product of probability measures preserves the
product measure. -/
theorem measurePreserving_update_pi (j : ι) :
    MeasurePreserving (fun p : (∀ i, X i) × X j => update p.1 j p.2)
      ((Measure.pi μ).prod (μ j)) (Measure.pi μ) := by
  refine ⟨measurable_update', (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (∀ i, X i) × X j => update p.1 j p.2) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (update s j Set.univ) ×ˢ s j := by
    ext ⟨x, a⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h j⟩
      by_cases hi : i = j
      · subst hi
        simp
      · simpa [update_of_ne hi] using h i
    · rintro ⟨h, ha⟩ i
      by_cases hi : i = j
      · subst hi
        simpa using ha
      · simpa [update_of_ne hi] using h i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hupd : ∀ i, μ i (update s j Set.univ i) = update (fun i => μ i (s i)) j 1 i := by
    intro i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [update_of_ne hi]
  simp_rw [hupd]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j), one_mul, mul_comm,
    Finset.sdiff_singleton_eq_erase]
  exact Finset.mul_prod_erase _ (fun i => μ i (s i)) (Finset.mem_univ j)

end Update

section Product

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {G : ι → Type v} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)]
variable (P : ∀ i, Subgroup (G i)) (K : ∀ i, Subgroup (G i))

/-- Coordinatewise inclusion of a family of elements of the subgroups `K i`. -/
def piVal (k : ∀ i, K i) : ∀ i, G i := fun i => (k i : G i)

omit [Fintype ι] [DecidableEq ι] [∀ i, IsTopologicalGroup (G i)] in
theorem continuous_piVal : Continuous (piVal K) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

omit [Fintype ι] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
theorem piVal_update (k : ∀ i, K i) (j : ι) (a : K j) :
    piVal K (update k j a) = update (piVal K k) j (a : G j) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [piVal]
  · simp [piVal, update_of_ne hi]

omit [Fintype ι] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
theorem update_mul_mulSingle (x : ∀ i, G i) (j : ι) (y h : G j) :
    update x j y * Pi.mulSingle j h = update x j (y * h) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [update_of_ne hi, Pi.mulSingle_eq_of_ne hi]

omit [Fintype ι] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
theorem mulSingle_mul_update (x : ∀ i, G i) (j : ι) (q y : G j) :
    Pi.mulSingle j q * update x j y = update x j (q * y) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [update_of_ne hi, Pi.mulSingle_eq_of_ne hi]

omit [Fintype ι] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
theorem mulSingle_mem_pi (j : ι) (q : P j) :
    Pi.mulSingle j (q : G j) ∈ Subgroup.pi Set.univ P := by
  intro i _
  by_cases hi : i = j
  · subst hi
    simp
  · simp [Pi.mulSingle_eq_of_ne hi, one_mem]

variable [∀ i, MeasurableSpace (K i)] [∀ i, BorelSpace (K i)]
  [∀ i, SecondCountableTopology (K i)] [∀ i, CompactSpace (K i)]
variable (μ : ∀ i, Measure (K i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [DecidableEq ι] [∀ i, IsTopologicalGroup (G i)] in
/-- Continuous scalar functions on the compact product are integrable. -/
theorem integrable_of_continuous_pi {F : (∀ i, K i) → ℂ} (hF : Continuous F) :
    Integrable F (Measure.pi μ) :=
  hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

/-- One coordinate step: invariance under right translation by an element
supported in one coordinate. -/
theorem integral_piVal_mul_mulSingle (δj : ∀ i, P i → ℝ≥0)
    (hblock : ∀ i (φ : G i → ℂ), IsLocallyConstant φ →
      (∀ (q : P i) (x : G i), φ ((q : G i) * x) = ((δj i q : ℝ) : ℂ) * φ x) →
      ∀ g : G i, (∫ k : K i, φ ((k : G i) * g) ∂μ i) = ∫ k : K i, φ (k : G i) ∂μ i)
    (δ : Subgroup.pi Set.univ P → ℝ≥0)
    (hδ : ∀ (j : ι) (q : P j) (q' : Subgroup.pi Set.univ P),
      (q' : ∀ i, G i) = Pi.mulSingle j (q : G j) → δ q' = δj j q)
    (φ : (∀ i, G i) → ℂ) (hφ : IsLocallyConstant φ)
    (hcov : ∀ (q : Subgroup.pi Set.univ P) (x : ∀ i, G i),
      φ ((q : ∀ i, G i) * x) = ((δ q : ℝ) : ℂ) * φ x)
    (j : ι) (h : G j) :
    (∫ k, φ (piVal K k * Pi.mulSingle j h) ∂Measure.pi μ) =
      ∫ k, φ (piVal K k) ∂Measure.pi μ := by
  have hmp := measurePreserving_update_pi μ j
  have hcont : ∀ g : ∀ i, G i, Continuous fun k : ∀ i, K i => φ (piVal K k * g) :=
    fun g => hφ.continuous.comp ((continuous_piVal K).mul continuous_const)
  have hlift : ∀ g : ∀ i, G i, (∫ k, φ (piVal K k * g) ∂Measure.pi μ) =
      ∫ p, φ (piVal K (update p.1 j p.2) * g) ∂((Measure.pi μ).prod (μ j)) := by
    intro g
    have hm := integral_map (μ := (Measure.pi μ).prod (μ j)) hmp.measurable.aemeasurable
      (f := fun k : ∀ i, K i => φ (piVal K k * g))
      (by rw [hmp.map_eq]; exact (hcont g).aestronglyMeasurable)
    rw [hmp.map_eq] at hm
    exact hm
  have hprod : ∀ g : ∀ i, G i,
      Integrable (fun p : (∀ i, K i) × K j => φ (piVal K (update p.1 j p.2) * g))
        ((Measure.pi μ).prod (μ j)) := by
    intro g
    exact ((hcont g).comp (continuous_update j)).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have h1 := hlift (Pi.mulSingle j h)
  have h2 := hlift 1
  simp only [mul_one] at h2
  rw [h1, h2, integral_prod _ (hprod _)]
  rw [show (fun p : (∀ i, K i) × K j => φ (piVal K (update p.1 j p.2))) =
      fun p => φ (piVal K (update p.1 j p.2) * 1) by simp only [mul_one],
    integral_prod _ (hprod 1)]
  congr 1
  funext x
  let ψ : G j → ℂ := fun y => φ (update (piVal K x) j y)
  have hψ : IsLocallyConstant ψ :=
    hφ.comp_continuous (continuous_const.update j continuous_id)
  have hcovψ : ∀ (q : P j) (y : G j), ψ ((q : G j) * y) = ((δj j q : ℝ) : ℂ) * ψ y := by
    intro q y
    simp only [ψ]
    rw [← mulSingle_mul_update]
    rw [← hδ j q ⟨_, mulSingle_mem_pi P j q⟩ rfl]
    exact hcov ⟨_, mulSingle_mem_pi P j q⟩ _
  have hb := hblock j ψ hψ hcovψ h
  simp only [ψ] at hb
  simp only [piVal_update, update_mul_mulSingle, mul_one]
  exact hb

/-- Invariance under right translation by elements supported in a finite set of
coordinates, by induction on that set. -/
theorem integral_piVal_mul_of_support (δj : ∀ i, P i → ℝ≥0)
    (hblock : ∀ i (φ : G i → ℂ), IsLocallyConstant φ →
      (∀ (q : P i) (x : G i), φ ((q : G i) * x) = ((δj i q : ℝ) : ℂ) * φ x) →
      ∀ g : G i, (∫ k : K i, φ ((k : G i) * g) ∂μ i) = ∫ k : K i, φ (k : G i) ∂μ i)
    (δ : Subgroup.pi Set.univ P → ℝ≥0)
    (hδ : ∀ (j : ι) (q : P j) (q' : Subgroup.pi Set.univ P),
      (q' : ∀ i, G i) = Pi.mulSingle j (q : G j) → δ q' = δj j q)
    (s : Finset ι) :
    ∀ (φ : (∀ i, G i) → ℂ), IsLocallyConstant φ →
      (∀ (q : Subgroup.pi Set.univ P) (x : ∀ i, G i),
        φ ((q : ∀ i, G i) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : ∀ i, G i, (∀ i ∉ s, g i = 1) →
        (∫ k, φ (piVal K k * g) ∂Measure.pi μ) = ∫ k, φ (piVal K k) ∂Measure.pi μ := by
  induction s using Finset.induction_on with
  | empty =>
    intro φ _ _ g hg
    have hg1 : g = 1 := funext fun i => hg i (Finset.notMem_empty i)
    simp [hg1]
  | insert j s hj ih =>
    intro φ hφ hcov g hg
    obtain ⟨g', hg'def⟩ : ∃ g' : ∀ i, G i, g' = update g j 1 := ⟨_, rfl⟩
    have hg' : ∀ i ∉ s, g' i = 1 := by
      intro i hi
      rw [hg'def]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [update_of_ne hij]
        exact hg i (by simp [hij, hi])
    have hsplit : g = Pi.mulSingle j (g j) * g' := by
      funext i
      rw [hg'def]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [update_of_ne hij, Pi.mulSingle_eq_of_ne hij]
    let ψ : (∀ i, G i) → ℂ := fun x => φ (x * g')
    have hψ : IsLocallyConstant ψ :=
      hφ.comp_continuous (continuous_id.mul continuous_const)
    have hcovψ : ∀ (q : Subgroup.pi Set.univ P) (x : ∀ i, G i),
        ψ ((q : ∀ i, G i) * x) = ((δ q : ℝ) : ℂ) * ψ x := by
      intro q x
      simp only [ψ, mul_assoc]
      exact hcov q (x * g')
    calc (∫ k, φ (piVal K k * g) ∂Measure.pi μ)
        = ∫ k, ψ (piVal K k * Pi.mulSingle j (g j)) ∂Measure.pi μ := by
          conv_lhs => rw [hsplit]
          simp only [ψ, mul_assoc]
      _ = ∫ k, ψ (piVal K k) ∂Measure.pi μ :=
          integral_piVal_mul_mulSingle P K μ δj hblock δ hδ ψ hψ hcovψ j (g j)
      _ = ∫ k, φ (piVal K k) ∂Measure.pi μ := ih φ hφ hcov g' hg'

/-- The product scalar property for the product of the probability measures. -/
theorem pi_scalarIntegral (δj : ∀ i, P i → ℝ≥0)
    (hblock : ∀ i (φ : G i → ℂ), IsLocallyConstant φ →
      (∀ (q : P i) (x : G i), φ ((q : G i) * x) = ((δj i q : ℝ) : ℂ) * φ x) →
      ∀ g : G i, (∫ k : K i, φ ((k : G i) * g) ∂μ i) = ∫ k : K i, φ (k : G i) ∂μ i)
    (δ : Subgroup.pi Set.univ P → ℝ≥0)
    (hδ : ∀ (j : ι) (q : P j) (q' : Subgroup.pi Set.univ P),
      (q' : ∀ i, G i) = Pi.mulSingle j (q : G j) → δ q' = δj j q)
    (φ : (∀ i, G i) → ℂ) (hφ : IsLocallyConstant φ)
    (hcov : ∀ (q : Subgroup.pi Set.univ P) (x : ∀ i, G i),
      φ ((q : ∀ i, G i) * x) = ((δ q : ℝ) : ℂ) * φ x) (g : ∀ i, G i) :
    Integrable (fun k => φ (piVal K k * g)) (Measure.pi μ) ∧
      (∫ k, φ (piVal K k * g) ∂Measure.pi μ) = ∫ k, φ (piVal K k) ∂Measure.pi μ :=
  ⟨integrable_of_continuous_pi K μ
      (hφ.continuous.comp ((continuous_piVal K).mul continuous_const)),
    integral_piVal_mul_of_support P K μ δj hblock δ hδ Finset.univ φ hφ hcov g
      (fun i hi => absurd (Finset.mem_univ i) hi)⟩

end Product

section Transport

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {G : ι → Type v} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)]
variable (P : ∀ i, Subgroup (G i)) (K : ∀ i, Subgroup (G i))

/-- Families of elements of the subgroups `K i` are the elements of their
product subgroup. -/
def piSubgroupHomeomorph : (∀ i, K i) ≃ₜ Subgroup.pi Set.univ K where
  toFun k := ⟨piVal K k, fun i _ => (k i).2⟩
  invFun x i := ⟨(x : ∀ i, G i) i, x.2 i (Set.mem_univ i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_piVal K).subtype_mk _
  continuous_invFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

omit [Fintype ι] [DecidableEq ι] [∀ i, IsTopologicalGroup (G i)] in
@[simp] theorem piSubgroupHomeomorph_val (k : ∀ i, K i) :
    ((piSubgroupHomeomorph K k : Subgroup.pi Set.univ K) : ∀ i, G i) = piVal K k := rfl

variable [∀ i, MeasurableSpace (K i)] [∀ i, BorelSpace (K i)]
  [∀ i, SecondCountableTopology (K i)] [∀ i, CompactSpace (K i)]
variable (μ : ∀ i, Measure (K i)) [∀ i, IsProbabilityMeasure (μ i)]
variable [MeasurableSpace (Subgroup.pi Set.univ K)] [BorelSpace (Subgroup.pi Set.univ K)]

/-- The product of the factor probability measures, transported to the
product subgroup. -/
def piSubgroupMeasure : Measure (Subgroup.pi Set.univ K) :=
  Measure.map (piSubgroupHomeomorph K).toMeasurableEquiv (Measure.pi μ)

omit [DecidableEq ι] [∀ i, IsTopologicalGroup (G i)] [∀ i, CompactSpace (K i)] in
/-- The transported product measure charges every nonempty open set when each
factor measure does. -/
theorem piSubgroupMeasure_isOpenPosMeasure [∀ i, (μ i).IsOpenPosMeasure] :
    (piSubgroupMeasure K μ).IsOpenPosMeasure :=
  (piSubgroupHomeomorph K).continuous.isOpenPosMeasure_map
    (piSubgroupHomeomorph K).surjective

/-- The product scalar property on the product subgroup: blockwise compact
average invariance gives integrability and invariance of the compact average
under every right translation of the product. -/
theorem piSubgroup_scalarIntegral (δj : ∀ i, P i → ℝ≥0)
    (hblock : ∀ i (φ : G i → ℂ), IsLocallyConstant φ →
      (∀ (q : P i) (x : G i), φ ((q : G i) * x) = ((δj i q : ℝ) : ℂ) * φ x) →
      ∀ g : G i, (∫ k : K i, φ ((k : G i) * g) ∂μ i) = ∫ k : K i, φ (k : G i) ∂μ i)
    (δ : Subgroup.pi Set.univ P → ℝ≥0)
    (hδ : ∀ (j : ι) (q : P j) (q' : Subgroup.pi Set.univ P),
      (q' : ∀ i, G i) = Pi.mulSingle j (q : G j) → δ q' = δj j q)
    (φ : (∀ i, G i) → ℂ) (hφ : IsLocallyConstant φ)
    (hcov : ∀ (q : Subgroup.pi Set.univ P) (x : ∀ i, G i),
      φ ((q : ∀ i, G i) * x) = ((δ q : ℝ) : ℂ) * φ x) (g : ∀ i, G i) :
    Integrable (fun k : Subgroup.pi Set.univ K => φ ((k : ∀ i, G i) * g))
        (piSubgroupMeasure K μ) ∧
      (∫ k : Subgroup.pi Set.univ K, φ ((k : ∀ i, G i) * g) ∂piSubgroupMeasure K μ) =
        ∫ k : Subgroup.pi Set.univ K, φ (k : ∀ i, G i) ∂piSubgroupMeasure K μ := by
  obtain ⟨hi, he⟩ := pi_scalarIntegral P K μ δj hblock δ hδ φ hφ hcov g
  refine ⟨?_, ?_⟩
  · rw [piSubgroupMeasure, integrable_map_equiv]
    exact hi
  · rw [piSubgroupMeasure, integral_map_equiv, integral_map_equiv]
    exact he

end Transport

end Langlands.Induction
