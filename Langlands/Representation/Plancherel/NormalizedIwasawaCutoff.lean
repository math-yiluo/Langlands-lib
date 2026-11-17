import Langlands.Representation.Plancherel.ProjectedCompactCutoff

/-! # Normalized cutoffs for arbitrary compact Iwasawa data -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open Aubert.General HarishChandraSchwartz

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G)
  [MeasurableSpace M] [BorelSpace M]
  (μM : Measure M) [μM.IsHaarMeasure]

/-- Normalize `1_(U K)` by its actual Levi orbit mass. -/
def normalizedIwasawaCutoff (g : G) : ℝ≥0∞ :=
  (μM (projectedCompactOpenSubgroup h K : Set M))⁻¹ * cutoff U K g

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [BorelSpace M] in
/-- The projected compact subgroup has strictly positive mass for any Haar
measure. -/
theorem projectedCompact_mass_ne_zero :
    μM (projectedCompactOpenSubgroup h K : Set M) ≠ 0 :=
  (projectedCompactOpenSubgroup h K).isOpen.measure_ne_zero _
    ⟨1, (projectedCompactOpenSubgroup h K).one_mem⟩

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [BorelSpace M] in
/-- The projected compact subgroup has finite Haar mass. -/
theorem projectedCompact_mass_ne_top (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hr : Continuous h.projection) :
    μM (projectedCompactOpenSubgroup h K : Set M) ≠ ⊤ :=
  (isCompact_projectedCompactOpenSubgroup h K hP hK hr).measure_ne_top

omit [SecondCountableTopology G] [BorelSpace M] [μM.IsHaarMeasure] in
/-- The normalized cutoff is measurable. -/
theorem measurable_normalizedIwasawaCutoff : Measurable (normalizedIwasawaCutoff h K μM) :=
  measurable_const.mul (measurable_cutoff K.isOpen)

/-- The normalized cutoff has left Levi orbit integral one. -/
theorem lintegral_normalizedIwasawaCutoff_inv_mul
    (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (g : G) :
    ∫⁻ m : M, normalizedIwasawaCutoff h K μM ((m : G)⁻¹ * g) ∂μM = 1 := by
  unfold normalizedIwasawaCutoff
  rw [lintegral_const_mul _
      (f := fun m : M => cutoff U K ((m : G)⁻¹ * g))
      ((measurable_cutoff K.isOpen).comp
        (continuous_subtype_val.measurable.inv.mul measurable_const)),
    lintegral_cutoff_inv_mul_projected h K μM hfac,
    ENNReal.inv_mul_cancel (projectedCompact_mass_ne_zero h K μM)
      (projectedCompact_mass_ne_top h K μM hP hK hr)]

/-- Right invariance gives the same normalized right orbit integral. -/
theorem lintegral_normalizedIwasawaCutoff_mul_left [μM.IsMulRightInvariant]
    (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (g : G) :
    ∫⁻ m : M, normalizedIwasawaCutoff h K μM ((m : G) * g) ∂μM = 1 := by
  unfold normalizedIwasawaCutoff
  rw [lintegral_const_mul _
      (f := fun m : M => cutoff U K ((m : G) * g))
      ((measurable_cutoff K.isOpen).comp
        (continuous_subtype_val.measurable.mul measurable_const)),
    lintegral_cutoff_mul_left_projected h K μM hfac,
    ENNReal.inv_mul_cancel (projectedCompact_mass_ne_zero h K μM)
      (projectedCompact_mass_ne_top h K μM hP hK hr)]

variable {P' V : Subgroup G} (h' : IsSemidirectDecomposition P' M V)
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  [SFinite μM] [μM.IsMulRightInvariant]

/-- The normalized opposite cutoffs give equal integrals on every nonnegative
left-Levi-invariant function, with no compact-splitting premise. -/
theorem lintegral_normalizedIwasawaCutoff_exchange
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection) (hr' : Continuous h'.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hfac' : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (Θ : G → ℝ≥0∞) (hΘ : Measurable Θ)
    (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) :
    ∫⁻ g, normalizedIwasawaCutoff h' K μM g * Θ g ∂μ =
      ∫⁻ g, normalizedIwasawaCutoff h K μM g * Θ g ∂μ := by
  let cU := normalizedIwasawaCutoff h K μM
  let cV := normalizedIwasawaCutoff h' K μM
  have hcU : Measurable cU := measurable_normalizedIwasawaCutoff h K μM
  have hcV : Measurable cV := measurable_normalizedIwasawaCutoff h' K μM
  have hval : Measurable fun m : M => (m : G) := continuous_subtype_val.measurable
  have hmeas1 : Measurable (Function.uncurry fun (g : G) (m : M) =>
      cV g * Θ g * cU ((m : G)⁻¹ * g)) :=
    ((hcV.comp measurable_fst).mul (hΘ.comp measurable_fst)).mul
      (hcU.comp ((hval.comp measurable_snd).inv.mul measurable_fst))
  have hmeas2 : Measurable (Function.uncurry fun (g : G) (m : M) =>
      cV ((m : G) * g) * Θ g * cU g) :=
    ((hcV.comp ((hval.comp measurable_snd).mul measurable_fst)).mul
      (hΘ.comp measurable_fst)).mul (hcU.comp measurable_fst)
  change ∫⁻ g, cV g * Θ g ∂μ = ∫⁻ g, cU g * Θ g ∂μ
  calc
    _ = ∫⁻ g, ∫⁻ m : M, cV g * Θ g * cU ((m : G)⁻¹ * g) ∂μM ∂μ := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul _
          (f := fun m : M => cU ((m : G)⁻¹ * g))
          (hcU.comp (hval.inv.mul measurable_const)),
        lintegral_normalizedIwasawaCutoff_inv_mul h K μM hP hK hr hfac, mul_one]
    _ = ∫⁻ m : M, ∫⁻ g, cV g * Θ g * cU ((m : G)⁻¹ * g) ∂μ ∂μM :=
      lintegral_lintegral_swap hmeas1.aemeasurable
    _ = ∫⁻ m : M, ∫⁻ g, cV ((m : G) * g) * Θ g * cU g ∂μ ∂μM := by
      refine lintegral_congr fun m => ?_
      rw [← lintegral_mul_left_eq_self _ (m : G)]
      refine lintegral_congr fun g => ?_
      rw [hinv, inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ m : M, cV ((m : G) * g) * Θ g * cU g ∂μM ∂μ :=
      (lintegral_lintegral_swap hmeas2.aemeasurable).symm
    _ = ∫⁻ g, cU g * Θ g ∂μ := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_mul_const _
          (f := fun m : M => cV ((m : G) * g) * Θ g)
          ((hcV.comp (hval.mul measurable_const)).mul measurable_const),
        lintegral_mul_const _ (f := fun m : M => cV ((m : G) * g))
          (hcV.comp (hval.mul measurable_const)),
        lintegral_normalizedIwasawaCutoff_mul_left h' K μM hP' hK hr' hfac',
        one_mul, mul_comm]

end Langlands.Plancherel.LeviInvariantIwasawaExchange
