import Langlands.Group.GL.LowerBlockQuotientGeometryProof
import Langlands.AllField.Group.GL.LowerBlockQuotientGeometryStatement
import Langlands.AllField.Group.GL.LowerTriangularBigCellConull
import Langlands.AllField.Group.GL.LowerTriangularQuotientCell
/-!
# Geometry of the lower-block quotient chart

The published chart `([g], x, h) ↦ [[[g,0],[x,h]]]` from `N_a \ GL_a × M_{d×a} × B⁻_d`
to `N_{a+d} \ GL_{a+d}` is an open embedding, is Borel measurable, and has conull
range for every compatible quotient measure. Openness: after right translation by
`diag(g₀, 1)`, the chart restricted to the big-cell parameters `([b g₀], x g₀, h)`
is the composite of block coordinates `B⁻_a × M × B⁻_d ≃ₜ B⁻_{a+d}` with the open
cell `B⁻_{a+d} → N_{a+d} \ GL_{a+d}`. These parameter sets cover. Conullness: the
range contains every coset of a lower triangular matrix, and these cosets are
conull.
-/

noncomputable section

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear hiding continuous_lowerBlockCellParameters exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular isOpenEmbedding_lowerBlockQuotientChart isOpenEmbedding_lowerTriangularQuotientMap isOpenMap_lowerBlockQuotientChart isOpenMap_lowerBlockQuotientChart_comp_cellParameters isOpen_upperUnipotent_mul_lowerTriangular_inter lowerBlockQuotientChart_range_compl_null measurable_lowerBlockQuotientChart padic_exists_ne_zero_mem_nhds_zero padic_lowerTriangular_leftQuotient_conull padic_setOf_not_upperUnipotent_mul_lowerTriangular
open Langlands.AllField.GeneralLinear

open _root_.Topology _root_.MeasureTheory
open Langlands.QuotientIntegration

universe u uF

section Algebra


end Algebra

section Padic

variable {F : Type uF} [Field F]

/-- The translated big-cell parameter map is continuous. -/
theorem continuous_lowerBlockCellParameters (T : LocalFieldData F) (a d : ℕ)
    (g₀ : GeneralLinear a F) :
    letI := T.topology
    Continuous (lowerBlockCellParameters (d := d) g₀) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup a
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (continuous_snd.comp continuous_snd))
  · exact (leftQuotient_isOpenQuotientMap _).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
  · exact (continuous_fst.comp continuous_snd).matrix_mul continuous_const

/-- On translated big-cell parameters the chart is an open map. -/
theorem isOpenMap_lowerBlockQuotientChart_comp_cellParameters (T : LocalFieldData F)
    (a d : ℕ) (g₀ : GeneralLinear a F) :
    letI := T.topology
    IsOpenMap (lowerBlockQuotientChart ∘ lowerBlockCellParameters (d := d) g₀) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (a + d)
  have hfun : lowerBlockQuotientChart ∘ lowerBlockCellParameters (d := d) g₀ =
      rightTranslate (upperUnipotent (a + d) F) (lowerBlockPair g₀ 0 1) ∘
        lowerTriangularQuotientMap (a + d) F ∘
          lowerTriangularBlockHomeomorph a d F := by
    funext z
    exact lowerBlockQuotientChart_lowerBlockCellParameters g₀ z
  rw [hfun]
  exact (rightTranslate _ _).isOpenMap.comp
    ((isOpenEmbedding_lowerTriangularQuotientMap T (a + d)).isOpenMap.comp
      (lowerTriangularBlockHomeomorph a d F).isOpenMap)

/-- The chart is an open map. -/
theorem isOpenMap_lowerBlockQuotientChart (T : LocalFieldData F) (a d : ℕ) :
    letI := T.topology
    IsOpenMap (lowerBlockQuotientChart (a := a) (d := d) (R := F)) := by
  let := T.topology
  intro W hW
  have hcover : lowerBlockQuotientChart '' W =
      ⋃ g₀ : GeneralLinear a F,
        (lowerBlockQuotientChart ∘ lowerBlockCellParameters (d := d) g₀) ''
          (lowerBlockCellParameters g₀ ⁻¹' W) := by
    ext q
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨g₀, z, rfl⟩ := exists_lowerBlockCellParameters_eq w
      exact Set.mem_iUnion.mpr ⟨g₀, z, hw, rfl⟩
    · intro hq
      obtain ⟨g₀, z, hz, rfl⟩ := Set.mem_iUnion.mp hq
      exact ⟨_, hz, rfl⟩
  rw [hcover]
  exact isOpen_iUnion fun g₀ => isOpenMap_lowerBlockQuotientChart_comp_cellParameters T a d g₀ _
    (hW.preimage (continuous_lowerBlockCellParameters T a d g₀))

/-- The chart is an open embedding. -/
theorem isOpenEmbedding_lowerBlockQuotientChart (T : LocalFieldData F) (a d : ℕ) :
    letI := T.topology
    IsOpenEmbedding (lowerBlockQuotientChart (a := a) (d := d) (R := F)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact .of_continuous_injective_isOpenMap continuous_lowerBlockQuotientChart
    lowerBlockQuotientChart_injective (isOpenMap_lowerBlockQuotientChart T a d)

/-- The chart is measurable for the Borel structures on the quotients, the
field and the lower triangular group, and the induced product structures. -/
theorem measurable_lowerBlockQuotientChart (T : LocalFieldData F) (a d : ℕ) :
    letI := T.topology
    letI := borel F
    letI := borel (LeftQuotient (upperUnipotent a F))
    letI := borel (LeftQuotient (upperUnipotent (a + d) F))
    letI := borel (lowerTriangularSubgroup d F)
    Measurable (lowerBlockQuotientChart (a := a) (d := d) (R := F)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent a F))
  have : BorelSpace (LeftQuotient (upperUnipotent a F)) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (a + d) F))
  have : BorelSpace (LeftQuotient (upperUnipotent (a + d) F)) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup d F)
  have : BorelSpace (lowerTriangularSubgroup d F) := ⟨rfl⟩
  have : SecondCountableTopology F := T.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin d) (Fin a) F) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin a → F))
  have := T.generalLinearSecondCountableTopology d
  have : SecondCountableTopology (lowerTriangularSubgroup d F) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact continuous_lowerBlockQuotientChart.measurable

set_option linter.overlappingInstances false in
/-- The range of the chart is conull for every compatible quotient measure: it
contains the conull set of cosets of lower triangular matrices. -/
theorem lowerBlockQuotientChart_range_compl_null (T : LocalFieldData F) (a d : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (GeneralLinear (a + d) F)
    letI : BorelSpace (GeneralLinear (a + d) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (a + d) F)
    letI : BorelSpace (upperUnipotent (a + d) F) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (a + d) F))
    letI : BorelSpace (LeftQuotient (upperUnipotent (a + d) F)) := ⟨rfl⟩
    ∀ (μG : Measure (GeneralLinear (a + d) F))
      (μH : Measure (upperUnipotent (a + d) F))
      [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
      [μH.IsMulRightInvariant] (μ : Measure (LeftQuotient (upperUnipotent (a + d) F))),
      IsCompatible (upperUnipotent (a + d) F) μG μH μ →
      μ (Set.range (lowerBlockQuotientChart (a := a) (d := d) (R := F)))ᶜ = 0 := by
  intro μG μH _ _ _ _ _ μ hμ
  refine measure_mono_null ?_ (padic_lowerTriangular_leftQuotient_conull T (a + d) μG μH μ hμ)
  intro q hq b hb hbq
  exact hq (hbq ▸ mk_lowerTriangular_mem_range_lowerBlockQuotientChart ⟨b, hb⟩)

end Padic

end Langlands.AllField.GeneralLinear

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LowerBlockQuotientGeometryStatement lowerBlockQuotientGeometry
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear hiding continuous_lowerBlockCellParameters exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular isOpenEmbedding_lowerBlockQuotientChart isOpenEmbedding_lowerTriangularQuotientMap isOpenMap_lowerBlockQuotientChart isOpenMap_lowerBlockQuotientChart_comp_cellParameters isOpen_upperUnipotent_mul_lowerTriangular_inter lowerBlockQuotientChart_range_compl_null measurable_lowerBlockQuotientChart padic_exists_ne_zero_mem_nhds_zero padic_lowerTriangular_leftQuotient_conull padic_setOf_not_upperUnipotent_mul_lowerTriangular
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- Proof of `LowerBlockQuotientGeometryStatement`: the actual lower-block chart
is an open measurable embedding with conull range. -/
theorem lowerBlockQuotientGeometry : LowerBlockQuotientGeometryStatement.{uF} := by
  intro F _ _ _ _ n k
  let := borel (Langlands.GeneralLinear (n + 1 + k + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + k + 1) F)
  have : BorelSpace (upperUnipotent (n + 1 + k + 1) F) := ⟨rfl⟩
  intro chart _ μ hμ
  exact ⟨isOpenEmbedding_lowerBlockQuotientChart (⟨⟩ : LocalFieldData F) (n + 1) (k + 1),
    measurable_lowerBlockQuotientChart (⟨⟩ : LocalFieldData F) (n + 1) (k + 1),
    lowerBlockQuotientChart_range_compl_null (⟨⟩ : LocalFieldData F) (n + 1) (k + 1)
      (generalLinearHaar F (n + 1 + k)) (unipotentHaar F (n + 1 + k)) μ hμ⟩

end Langlands.AllField.RankinSelberg
