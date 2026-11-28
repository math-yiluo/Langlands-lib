import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # Haar packing for a discrete subgroup -/

noncomputable section

universe u

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.MeasureTheory

/-- A compact neighborhood can be chosen inside any prescribed neighborhood
to bound the number of subgroup points in a compact set by a volume ratio. -/
def DiscreteSubgroupHaarPackingStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G), IsDiscrete (Γ : Set G) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] {Z : Set G}, Z ∈ 𝓝 (1 : G) →
      ∃ W : Set G, IsCompact W ∧ W ∈ 𝓝 (1 : G) ∧ W ⊆ Z ∧
        0 < (μ W).toReal ∧
        ∀ {D : Set G}, IsCompact D →
          ((Γ : Set G) ∩ D).Finite ∧
            (((Γ : Set G) ∩ D).ncard : ℝ) ≤ (μ (D * W)).toReal / (μ W).toReal

theorem discreteSubgroupHaarPacking : DiscreteSubgroupHaarPackingStatement.{u} := by
  classical
  intro G _ _ _ _ _ _ _ Γ hΓ μ _ Z hZ
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have h1U : (1 : G) ∈ U := by
    change (1 : Γ) ∈ Subtype.val ⁻¹' U
    rw [hUeq]
    exact mem_singleton _
  have hiso (g : G) (hg : g ∈ Γ) (hgU : g ∈ U) : g = 1 := by
    have h : (⟨g, hg⟩ : Γ) ∈ Subtype.val ⁻¹' U := hgU
    rw [hUeq] at h
    exact congrArg Subtype.val (mem_singleton_iff.mp h)
  have hdiv : (fun q : G × G => q.1 * q.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
    (continuous_fst.mul continuous_snd.inv).continuousAt.preimage_mem_nhds (by
      simpa using hU.mem_nhds h1U)
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.mp hdiv
  obtain ⟨W, ⟨hWn, hWc⟩, hW⟩ :=
    (compact_basis_nhds (1 : G)).mem_iff.mp (inter_mem (inter_mem hV₁ hV₂) hZ)
  have hWpos : 0 < (μ W).toReal :=
    ENNReal.toReal_pos (measure_pos_of_mem_nhds μ hWn).ne' hWc.measure_lt_top.ne
  refine ⟨W, hWc, hWn, fun x hx => (hW hx).2, hWpos, ?_⟩
  intro D hDc
  let P := (Γ : Set G) ∩ D
  have hPc : IsCompact P := hDc.inter_left Subgroup.isClosed_of_discreteTopology
  have hPf : P.Finite := hPc.finite (hΓ.mono inter_subset_left)
  let A (g : G) := (g * ·) '' W
  have hAc (g : G) : IsCompact (A g) := hWc.image (continuous_const.mul continuous_id)
  have hdis : PairwiseDisjoint (↑hPf.toFinset : Set G) A := by
    intro g hg g' hg' hne
    have hgΓ : g ∈ Γ := (hPf.mem_toFinset.mp hg).1
    have hg'Γ : g' ∈ Γ := (hPf.mem_toFinset.mp hg').1
    refine disjoint_left.mpr ?_
    rintro z ⟨w, hw, rfl⟩ ⟨w', hw', heq⟩
    change g' * w' = g * w at heq
    have hrel : g'⁻¹ * g = w' * w⁻¹ := by
      calc
        g'⁻¹ * g = g'⁻¹ * (g * w) * w⁻¹ := by group
        _ = w' * w⁻¹ := by rw [← heq]; group
    have hunit : g'⁻¹ * g = 1 := by
      apply hiso _ (Γ.mul_mem (Γ.inv_mem hg'Γ) hgΓ)
      rw [hrel]
      exact hV (show (w', w) ∈ V₁ ×ˢ V₂ from ⟨(hW hw').1.1, (hW hw).1.2⟩)
    apply hne
    calc
      g = g' * (g'⁻¹ * g) := by group
      _ = g' := by rw [hunit, mul_one]
  have hsub : (⋃ g ∈ hPf.toFinset, A g) ⊆ D * W := by
    refine iUnion₂_subset fun g hg => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact mul_mem_mul (hPf.mem_toFinset.mp hg).2 hw
  have hmass (g : G) : μ (A g) = μ W := by
    have hpre : A g = (g⁻¹ * ·) ⁻¹' W := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [mul_assoc] using hw
      · intro hz
        exact ⟨g⁻¹ * z, hz, by simp⟩
    rw [hpre, measure_preimage_mul]
  have hbound : (P.ncard : ℝ≥0∞) * μ W ≤ μ (D * W) := calc
    _ = μ (⋃ g ∈ hPf.toFinset, A g) := by
      rw [measure_biUnion_finset hdis (fun g _ => (hAc g).measurableSet)]
      simp only [hmass, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hPf]
    _ ≤ _ := measure_mono hsub
  have hreal := ENNReal.toReal_mono (hDc.mul hWc).measure_lt_top.ne hbound
  refine ⟨hPf, (le_div_iff₀ hWpos).mpr ?_⟩
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

end Langlands.MeasureTheory
