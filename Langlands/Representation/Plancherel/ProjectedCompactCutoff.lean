import Langlands.Representation.Plancherel.LeviInvariantIwasawaExchange
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Aubert.General.SemidirectHaarModulus

/-! # Levi averages of Iwasawa cutoffs without compact splitting -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Pointwise

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open Aubert.General Induction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G)

/-- The Levi projection of `P ∩ K`, with its inherited open subgroup structure.
Compactness follows separately from continuity of the projection. -/
def projectedCompactOpenSubgroup : OpenSubgroup M where
  toSubgroup := (conjOpenSubgroup P K 1).toSubgroup.map h.projection
  isOpen' := by
    apply Subgroup.isOpen_mono
      (H₁ := (K.comap M.subtype continuous_subtype_val).toSubgroup)
    · intro m hm
      refine Subgroup.mem_map.mpr ⟨⟨m, h.levi_le m.2⟩, ?_, h.projection_levi m⟩
      change (m : G) ∈ K at hm
      apply mem_conjOpenSubgroup.mpr
      simpa only [inv_one, one_mul, mul_one] using hm
    · exact (K.comap M.subtype continuous_subtype_val).isOpen

/-- Membership means a compact-parabolic representative has the given Levi
projection. -/
theorem mem_projectedCompactOpenSubgroup (m : M) :
    m ∈ projectedCompactOpenSubgroup h K ↔
      ∃ p : P, (p : G) ∈ K ∧ h.projection p = m := by
  change (∃ p, p ∈ conjOpenSubgroup P K 1 ∧ h.projection p = m) ↔ _
  simp only [mem_conjOpenSubgroup, inv_one, one_mul, mul_one]

/-- The projected open subgroup is compact for the same supplied compact open
`K`, without stability of `P ∩ K` under the Levi projection. -/
theorem isCompact_projectedCompactOpenSubgroup (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hr : Continuous h.projection) :
    IsCompact (projectedCompactOpenSubgroup h K : Set M) := by
  have hc := (isCompact_conjOpenSubgroup P hP K hK 1).image hr
  change IsCompact ((conjOpenSubgroup P K 1).toSubgroup.map h.projection : Set M)
  rw [Subgroup.coe_map]
  exact hc

/-- A cutoff by `U K` detects the projected compact subgroup, rather than the
literal intersection `M ∩ K`. -/
theorem mem_cutoffSet_iff_projected (m : M) (u : U) {k : G} (hk : k ∈ K) :
    (m : G) * u * k ∈ cutoffSet U K ↔ m ∈ projectedCompactOpenSubgroup h K := by
  constructor
  · rintro ⟨u', hu', k', hk', he⟩
    have hconj : (m : G)⁻¹ * u'⁻¹ * (m : G) ∈ U := by
      have hh := (Subgroup.mem_normalizer_iff.mp
        (h.levi_le_normalizer (M.inv_mem m.2)) u'⁻¹).mp (U.inv_mem hu')
      simpa only [inv_inv] using hh
    let u₀ : U := ⟨(m : G)⁻¹ * u'⁻¹ * (m : G) * u, U.mul_mem hconj u.2⟩
    have hmem : (m : G) * u₀ ∈ K := by
      have he' : (m : G) * u₀ = k' * k⁻¹ := by
        change (m : G) * ((m : G)⁻¹ * u'⁻¹ * (m : G) * u) = _
        calc
          _ = u'⁻¹ * ((m : G) * u * k) * k⁻¹ := by group
          _ = u'⁻¹ * (u' * k') * k⁻¹ := by rw [← he]
          _ = _ := by group
      rw [he']
      exact K.mul_mem hk' (K.inv_mem hk)
    apply (mem_projectedCompactOpenSubgroup h K m).mpr
    exact ⟨⟨m, h.levi_le m.2⟩ * ⟨u₀, h.unipotent_le u₀.2⟩,
      hmem, h.projection_mul m u₀⟩
  · intro hm
    obtain ⟨p, hp, hpm⟩ := (mem_projectedCompactOpenSubgroup h K m).mp hm
    let u₀ : U := ⟨(m : G)⁻¹ * (p : G), by
      rw [← hpm]
      exact h.projection_inv_mul_mem p⟩
    have hp' : (p : G) = (m : G) * u₀ := by simp [u₀]
    refine ⟨(m : G) * ((u : G) * (u₀ : G)⁻¹) * (m : G)⁻¹, ?_,
      (p : G) * k, K.mul_mem hp hk, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (h.levi_le_normalizer m.2) _).mp
        (U.mul_mem u.2 (U.inv_mem u₀.2))
    · rw [hp']
      group

/-- The exact cutoff identity on Iwasawa coordinates, with no compact splitting
premise. -/
theorem cutoff_mul_projected (m : M) (u : U) {k : G} (hk : k ∈ K) :
    cutoff U K ((m : G) * u * k) =
      (projectedCompactOpenSubgroup h K : Set M).indicator 1 m := by
  unfold cutoff
  by_cases hm : m ∈ projectedCompactOpenSubgroup h K
  · rw [Set.indicator_of_mem ((mem_cutoffSet_iff_projected h K m u hk).mpr hm),
      Set.indicator_of_mem hm]
    rfl
  · rw [Set.indicator_of_notMem
      (fun hh => hm ((mem_cutoffSet_iff_projected h K m u hk).mp hh)),
      Set.indicator_of_notMem hm]

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace M] [BorelSpace M]
  (μM : Measure M) [μM.IsMulLeftInvariant]

omit [MeasurableSpace G] [BorelSpace G] in
/-- The left Levi average of `1_(U K)` is the mass of the actual projected
compact subgroup, independently of the evaluation point. -/
theorem lintegral_cutoff_inv_mul_projected
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (g : G) :
    ∫⁻ m : M, cutoff U K ((m : G)⁻¹ * g) ∂μM =
      μM (projectedCompactOpenSubgroup h K : Set M) := by
  obtain ⟨m₀, u, k, hk, rfl⟩ := hfac g
  have he : ∀ m : M, cutoff U K ((m : G)⁻¹ * ((m₀ : G) * u * k)) =
      ((fun m => m₀⁻¹ * m) ⁻¹'
        (projectedCompactOpenSubgroup h K : Set M)).indicator 1 m := by
    intro m
    have h1 : (m : G)⁻¹ * ((m₀ : G) * u * k) = ((m⁻¹ * m₀ : M) : G) * u * k := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [h1, cutoff_mul_projected h K _ u hk]
    have hm : m⁻¹ * m₀ ∈ projectedCompactOpenSubgroup h K ↔
        m₀⁻¹ * m ∈ projectedCompactOpenSubgroup h K := by
      constructor
      · intro hh
        have hh' : (m⁻¹ * m₀)⁻¹ ∈ projectedCompactOpenSubgroup h K :=
          (projectedCompactOpenSubgroup h K).inv_mem hh
        simpa only [mul_inv_rev, inv_inv] using hh'
      · intro hh
        have hh' : (m₀⁻¹ * m)⁻¹ ∈ projectedCompactOpenSubgroup h K :=
          (projectedCompactOpenSubgroup h K).inv_mem hh
        simpa only [mul_inv_rev, inv_inv] using hh' 
    by_cases hh : m⁻¹ * m₀ ∈ projectedCompactOpenSubgroup h K
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem
        (show m ∈ (fun m => m₀⁻¹ * m) ⁻¹'
          (projectedCompactOpenSubgroup h K : Set M) from hm.mp hh)]
      rfl
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem
        (show m ∉ (fun m => m₀⁻¹ * m) ⁻¹'
          (projectedCompactOpenSubgroup h K : Set M) from fun hh' => hh (hm.mpr hh'))]
  simp_rw [he]
  rw [lintegral_indicator_one
      ((measurable_const_mul _) (projectedCompactOpenSubgroup h K).isOpen.measurableSet),
    measure_preimage_mul]

omit [MeasurableSpace G] [BorelSpace G] [μM.IsMulLeftInvariant] in
/-- The right Levi average has the same constant when Levi Haar is right
invariant. -/
theorem lintegral_cutoff_mul_left_projected [μM.IsMulRightInvariant]
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (g : G) :
    ∫⁻ m : M, cutoff U K ((m : G) * g) ∂μM =
      μM (projectedCompactOpenSubgroup h K : Set M) := by
  obtain ⟨m₀, u, k, hk, rfl⟩ := hfac g
  have he : ∀ m : M, cutoff U K ((m : G) * ((m₀ : G) * u * k)) =
      ((fun m => m * m₀) ⁻¹'
        (projectedCompactOpenSubgroup h K : Set M)).indicator 1 m := by
    intro m
    have h1 : (m : G) * ((m₀ : G) * u * k) = ((m * m₀ : M) : G) * u * k := by
      simp only [Subgroup.coe_mul]
      group
    rw [h1, cutoff_mul_projected h K _ u hk]
    rfl
  simp_rw [he]
  rw [lintegral_indicator_one
      ((measurable_mul_const _) (projectedCompactOpenSubgroup h K).isOpen.measurableSet),
    measure_preimage_mul_right]

end Langlands.Plancherel.LeviInvariantIwasawaExchange
