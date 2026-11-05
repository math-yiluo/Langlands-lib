import Langlands.Representation.Unitary.HermitianNeighborhoodWeightStatement

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uG

/-- Symmetrize a Urysohn bump and normalize its positive integral. -/
theorem hermitianNeighborhoodWeight : HermitianNeighborhoodWeightStatement.{uG} := by
  intro G _ _ _ _ _ _ _ μ _ _ d hd U hU
  have hIone : (1 : G) ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  let V : Set G := interior U ∩ (fun g : G => g⁻¹) ⁻¹' interior U
  have hVopen : IsOpen V := isOpen_interior.inter (isOpen_interior.preimage continuous_inv)
  have hVone : ({1} : Set G) ⊆ V := by
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨hIone, by simpa using hIone⟩
  obtain ⟨φ, hφeq, hφcompact, hφsupport, hφbounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hVopen hVone
  have hφone : φ 1 = 1 := by simpa using hφeq (by simp : (1 : G) ∈ ({1} : Set G))
  have hφcs : HasCompactSupport (φ : G → ℝ) := hφcompact
  let ψ : G → ℝ := fun g => φ g + (d g : ℝ) * φ g⁻¹
  have hψcont : Continuous ψ :=
    φ.continuous.add ((NNReal.continuous_coe.comp hd).mul (φ.continuous.comp continuous_inv))
  have hψcompact : HasCompactSupport ψ :=
    hφcs.add ((hφcs.comp_homeomorph (Homeomorph.inv G)).mul_left)
  have hψsupport : tsupport ψ ⊆ U := by
    intro g hg
    rcases tsupport_add (φ : G → ℝ) (fun g => (d g : ℝ) * φ g⁻¹) hg with hg | hg
    · exact interior_subset (hφsupport hg).1
    · have hinv : g⁻¹ ∈ tsupport φ :=
        tsupport_comp_subset_preimage (φ : G → ℝ) continuous_inv
          (tsupport_mul_subset_right hg)
      have hback := (hφsupport hinv).2
      exact interior_subset (by simpa using hback)
  have hψnonneg : ∀ g, 0 ≤ ψ g := fun g =>
    add_nonneg (hφbounds g).1 (mul_nonneg (d g).coe_nonneg (hφbounds g⁻¹).1)
  have hψone : ψ 1 = 2 := by norm_num [ψ, hφone]
  have hψhermitian (g : G) : ψ g = (d g : ℝ) * ψ g⁻¹ := by
    have hdinv : (d g : ℝ) * (d g⁻¹ : ℝ) = 1 := by
      rw [← NNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, NNReal.coe_one]
    dsimp [ψ]
    rw [inv_inv, mul_add, ← mul_assoc, hdinv, one_mul, add_comm]
  have hψint : Integrable ψ μ := hψcont.integrable_of_hasCompactSupport hψcompact
  let c : ℝ := ∫ g, ψ g ∂μ
  have hc : 0 < c := hψcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hψcompact hψnonneg (by rw [hψone]; norm_num)
  refine ⟨fun g => ψ g / c, hψcont.div_const c, ?_, ?_, ?_, hψint.div_const c, ?_, ?_⟩
  · apply IsCompact.of_isClosed_subset hψcompact (isClosed_tsupport (fun g => ψ g / c))
    exact tsupport_mul_subset_left
  · exact (show tsupport (fun g => ψ g / c) ⊆ tsupport ψ from
      tsupport_mul_subset_left).trans hψsupport
  · exact fun g => div_nonneg (hψnonneg g) hc.le
  · rw [integral_div]
    exact div_self (ne_of_gt hc)
  · intro g
    change ψ g / c = (d g : ℝ) * (ψ g⁻¹ / c)
    rw [hψhermitian g, mul_div_assoc]

end Langlands.Analysis
