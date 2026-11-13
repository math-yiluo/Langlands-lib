import Langlands.Representation.Jacquet.CoinvariantSubrepresentationRelationsProof

/-! # Haar averaging detects compact-subgroup coinvariant relations -/

noncomputable section

namespace Langlands.Jacquet

open MeasureTheory

universe uH uV

section Compact

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

/-- On a compact group the Haar projector is the finite orbit-mean projector. -/
theorem compactFixedProjection_eq_averageMap
    (μ : Measure H) [μ.IsHaarMeasure] (τ : Representation ℂ H E) (hτ : IsSmooth τ)
    (v : E) :
    (Hecke.fixedProjection μ τ hτ ⊤ isCompact_univ v : E) =
      Compact.averageMap τ hτ ⊤ isCompact_univ v := by
  let M := Compact.averageMap τ hτ ⊤ isCompact_univ
  let T : τ.IntertwiningMap τ :=
    { toLinearMap := M
      isIntertwining' := by
        intro g
        ext x
        change M (τ g x) = τ g (M x)
        calc
          M (τ g x) = M x :=
            Compact.orbitMean_apply (τ.comp (⊤ : OpenSubgroup H).toSubgroup.subtype)
              ⟨g, Subgroup.mem_top g⟩ x
          _ = τ g (M x) :=
            (Compact.averageMap_mem_fixedVectors τ hτ ⊤ isCompact_univ x
              ⟨g, Subgroup.mem_top g⟩).symm }
  have hc := congrArg (fun x : fixedVectors τ (⊤ : OpenSubgroup H).toSubgroup =>
    (x : E)) (Hecke.fixedProjection_intertwiner μ τ hτ ⊤ isCompact_univ hτ T v)
  change M (Hecke.fixedProjection μ τ hτ ⊤ isCompact_univ v : E) =
    (Hecke.fixedProjection μ τ hτ ⊤ isCompact_univ (M v) : E) at hc
  rw [Compact.averageMap_id τ hτ ⊤ isCompact_univ _
      (Hecke.fixedProjection μ τ hτ ⊤ isCompact_univ v).property] at hc
  have hMv := Compact.averageMap_mem_fixedVectors τ hτ ⊤ isCompact_univ v
  exact hc.trans
    (Hecke.heckeAction_normalizedIndicator_of_fixed μ τ hτ ⊤ isCompact_univ hMv)

/-- The kernel of the compact-group Haar projector is the group-relation span. -/
theorem compactFixedProjection_eq_zero_iff
    (μ : Measure H) [μ.IsHaarMeasure] (τ : Representation ℂ H E) (hτ : IsSmooth τ)
    (v : E) :
    (Hecke.fixedProjection μ τ hτ ⊤ isCompact_univ v : E) = 0 ↔
      v ∈ Representation.Coinvariants.ker τ := by
  rw [compactFixedProjection_eq_averageMap μ τ hτ v,
    Compact.averageMap_eq_zero_iff τ hτ ⊤ isCompact_univ v]
  change v ∈ relations τ ⊤ ↔ _
  rw [relations_top_eq_ker]

end Compact

/-- Renard III.2.9, the Proposition characterizing relations by compact averages. -/
theorem compactAveragingRelation :
    CompactAveragingRelationStatement.{uH, uV} := by
  intro H _ _ _ _ _ _ hcover hfilter E _ _ τ hτ v
  rw [relations_top_eq_ker]
  constructor
  · intro hv
    obtain ⟨K, hK, hvK⟩ := (Langlands.coinvariants_mem_ker_iff_compact
      (compactOpenFiniteContainment H hcover hfilter) τ v).mp hv
    refine ⟨K.toSubgroup, hK, ?_⟩
    let : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp hK
    let : MeasurableSpace K.toSubgroup := borel K.toSubgroup
    let : BorelSpace K.toSubgroup := ⟨rfl⟩
    intro μ _
    exact (compactFixedProjection_eq_zero_iff μ (τ.comp K.toSubgroup.subtype)
      (isSmooth_comp K.toSubgroup.subtype continuous_subtype_val hτ) v).mpr hvK
  · rintro ⟨K, hK, hvK⟩
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let : MeasurableSpace K := borel K
    let : BorelSpace K := ⟨rfl⟩
    have hv := (compactFixedProjection_eq_zero_iff Measure.haar (τ.comp K.subtype)
      (isSmooth_comp K.subtype continuous_subtype_val hτ) v).mp (hvK Measure.haar)
    exact Langlands.coinvariants_ker_comp_subgroup_le τ K hv

end Langlands.Jacquet
