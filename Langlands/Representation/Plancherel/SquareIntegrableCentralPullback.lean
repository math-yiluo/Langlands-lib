import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness

/-! # Transport of square-integrable central data under a group isomorphism -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel

open HarishChandraSchwartz

universe uG uH uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] (e : H ≃ₜ* G)
  (C : Subgroup G)

/-- The inverse image of a central subgroup under an isomorphism is central. -/
theorem centralSubgroup_comap_le_center (hC : C ≤ Subgroup.center G) :
    C.comap e.toMonoidHom ≤ Subgroup.center H :=
  (Subgroup.comap_mono hC).trans (Subgroup.comap_center_le_center e.injective)

variable [C.Normal]

/-- Quotients by a central subgroup and by its literal preimage are
continuously isomorphic. -/
def centralSubgroupPullbackQuotientEquiv : (H ⧸ C.comap e.toMonoidHom) ≃ₜ* (G ⧸ C) :=
  quotientContinuousMulEquiv e C (C.comap e.toMonoidHom)
    (Subgroup.map_comap_eq_self_of_surjective e.surjective C)

variable [MeasurableSpace (G ⧸ C)] [MeasurableSpace (H ⧸ C.comap e.toMonoidHom)]
  (μ : Measure (G ⧸ C))

/-- Pull the displayed quotient measure back along the quotient isomorphism. -/
def centralSubgroupPullbackMeasure : Measure (H ⧸ C.comap e.toMonoidHom) :=
  μ.map (centralSubgroupPullbackQuotientEquiv e C).symm

variable [BorelSpace (G ⧸ C)] [BorelSpace (H ⧸ C.comap e.toMonoidHom)]

instance centralSubgroupPullbackMeasure_isHaarMeasure
    [IsTopologicalGroup G] [IsTopologicalGroup H] [μ.IsHaarMeasure] :
    (centralSubgroupPullbackMeasure e C μ).IsHaarMeasure :=
  (centralSubgroupPullbackQuotientEquiv e C).symm.isHaarMeasure_map μ

/-- Mapping the pulled-back measure forward recovers its exact original scale. -/
theorem centralSubgroupPullbackMeasure_map :
    (centralSubgroupPullbackMeasure e C μ).map (centralSubgroupPullbackQuotientEquiv e C) = μ := by
  let φ := centralSubgroupPullbackQuotientEquiv e C
  change (μ.map φ.symm).map φ = μ
  rw [Measure.map_map (map_continuous φ).measurable (map_continuous φ.symm).measurable]
  rw [show (φ : _ → _) ∘ (φ.symm : _ → _) = id from funext φ.apply_symm_apply,
    Measure.map_id]

/-- The exact original square-integrability condition transfers under the
same group isomorphism and the pulled-back Haar measure. -/
theorem isSquareIntegrableModCentralSubgroup_pullback
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (hC : C ≤ Subgroup.center G) (ρ : Representation ℂ G V) [μ.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ μ) :
    IsSquareIntegrableModCentralSubgroup (C.comap e.toMonoidHom)
      (centralSubgroup_comap_le_center e C hC) (ρ.comp e.toMonoidHom)
      (centralSubgroupPullbackMeasure e C μ) :=
  (isSquareIntegrableModCentralSubgroup_comp_iff e C hC
    (C.comap e.toMonoidHom) (centralSubgroup_comap_le_center e C hC)
    (Subgroup.map_comap_eq_self_of_surjective e.surjective C) μ
    (centralSubgroupPullbackMeasure e C μ) (centralSubgroupPullbackMeasure_map e C μ) ρ).mpr hsq

omit [C.Normal] [MeasurableSpace (G ⧸ C)] [MeasurableSpace (H ⧸ C.comap e.toMonoidHom)]
  [BorelSpace (G ⧸ C)] [BorelSpace (H ⧸ C.comap e.toMonoidHom)] in
/-- Pullback of the indexed characters transports their common kernel literally. -/
theorem commonNormKernel_pullback {I : Type uI} (ν : I → (G →* ℝ≥0ˣ)) :
    commonNormKernel (fun i => (ν i).comp e.toMonoidHom) =
      (commonNormKernel ν).comap e.toMonoidHom := by
  ext x
  simp only [mem_commonNormKernel, MonoidHom.comp_apply, Subgroup.mem_comap]

omit [MeasurableSpace (G ⧸ C)] [MeasurableSpace (H ⧸ C.comap e.toMonoidHom)]
  [BorelSpace (G ⧸ C)] [BorelSpace (H ⧸ C.comap e.toMonoidHom)] in
/-- The finite quotient by the central subgroup and the common norm kernel
is preserved by the same isomorphism. -/
theorem finite_normKernel_sup_centralSubgroup_pullback
    {I : Type uI} (ν : I → (G →* ℝ≥0ˣ)) [Finite (G ⧸ (commonNormKernel ν ⊔ C))] :
    Finite (H ⧸ (commonNormKernel (fun i => (ν i).comp e.toMonoidHom) ⊔
      C.comap e.toMonoidHom)) := by
  have hmap : (commonNormKernel (fun i => (ν i).comp e.toMonoidHom) ⊔
      C.comap e.toMonoidHom).map e.toMonoidHom = commonNormKernel ν ⊔ C := by
    rw [commonNormKernel_pullback, Subgroup.map_sup,
      Subgroup.map_comap_eq_self_of_surjective e.surjective,
      Subgroup.map_comap_eq_self_of_surjective e.surjective]
  exact Finite.of_injective _ (QuotientGroup.congr _ _ e.toMulEquiv hmap).injective

end Langlands.Plancherel
