import Langlands.Group.GL.LowerTriangularBlockCoordinates
import Langlands.Group.GL.LowerTriangularQuotientCell
import Langlands.Group.GL.LowerTriangularBigCellConull
import Langlands.Group.GL.LowerBlockQuotientGeometryStatement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

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

namespace Langlands.GeneralLinear

open Topology Langlands.QuotientIntegration MeasureTheory

universe u uF

section Algebra

variable {R : Type u} [CommRing R] {a d : ℕ}

/-- Right-translated big-cell parameters `(b, x, h) ↦ ([b g₀], x g₀, h)`. -/
def lowerBlockCellParameters (g₀ : GeneralLinear a R)
    (z : lowerTriangularSubgroup a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    LowerBlockQuotientParameters a d R :=
  (Quotient.mk _ (z.1.val * g₀), z.2.1 * g₀.val, z.2.2)

/-- On translated big-cell parameters the chart is the coset of the block
coordinates, right multiplied by `diag(g₀, 1)`. -/
theorem lowerBlockQuotientChart_lowerBlockCellParameters (g₀ : GeneralLinear a R)
    (z : lowerTriangularSubgroup a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    lowerBlockQuotientChart (lowerBlockCellParameters g₀ z) =
      (Quotient.mk _ ((lowerTriangularBlockMap a d R z).val * lowerBlockPair g₀ 0 1) :
        LeftQuotient (upperUnipotent (a + d) R)) := by
  change (Quotient.mk _ (lowerBlockPair (z.1.val * g₀) (z.2.1 * g₀.val) z.2.2) :
    LeftQuotient (upperUnipotent (a + d) R)) = _
  rw [lowerTriangularBlockMap_val, lowerBlockPair_mul_lowerBlockPair, Matrix.mul_zero, add_zero,
    mul_one]

/-- Every parameter is a translated big-cell parameter: `([g], x, h)` is the
image of `(1, x g⁻¹, h)` for `g₀ = g`. -/
theorem exists_lowerBlockCellParameters_eq (w : LowerBlockQuotientParameters a d R) :
    ∃ (g₀ : GeneralLinear a R)
      (z : lowerTriangularSubgroup a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R),
      lowerBlockCellParameters g₀ z = w := by
  obtain ⟨q, x, h⟩ := w
  induction q using Quotient.inductionOn with
  | h g =>
    refine ⟨g, (1, x * (g⁻¹ : GeneralLinear a R).val, h), ?_⟩
    simp only [lowerBlockCellParameters, OneMemClass.coe_one, one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]

/-- The coset of a lower triangular matrix lies in the range of the chart. -/
theorem mk_lowerTriangular_mem_range_lowerBlockQuotientChart
    (b : lowerTriangularSubgroup (a + d) R) :
    (Quotient.mk _ b.val : LeftQuotient (upperUnipotent (a + d) R)) ∈
      Set.range (lowerBlockQuotientChart (a := a) (d := d) (R := R)) :=
  ⟨(Quotient.mk _ (lowerTriangularFirstBlock b).val, lowerTriangularRectangle b,
      lowerTriangularLastBlock b),
    congrArg (fun k : lowerTriangularSubgroup (a + d) R =>
        (Quotient.mk _ k.val : LeftQuotient (upperUnipotent (a + d) R)))
      ((lowerTriangularBlockEquiv a d R).apply_symm_apply b)⟩

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The translated big-cell parameter map is continuous. -/
theorem continuous_lowerBlockCellParameters (T : F.TopologicalData) (a d : ℕ)
    (g₀ : GeneralLinear a F.Carrier) :
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
theorem isOpenMap_lowerBlockQuotientChart_comp_cellParameters (T : F.TopologicalData)
    (a d : ℕ) (g₀ : GeneralLinear a F.Carrier) :
    letI := T.topology
    IsOpenMap (lowerBlockQuotientChart ∘ lowerBlockCellParameters (d := d) g₀) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (a + d)
  have hfun : lowerBlockQuotientChart ∘ lowerBlockCellParameters (d := d) g₀ =
      rightTranslate (upperUnipotent (a + d) F.Carrier) (lowerBlockPair g₀ 0 1) ∘
        lowerTriangularQuotientMap (a + d) F.Carrier ∘
          lowerTriangularBlockHomeomorph a d F.Carrier := by
    funext z
    exact lowerBlockQuotientChart_lowerBlockCellParameters g₀ z
  rw [hfun]
  exact (rightTranslate _ _).isOpenMap.comp
    ((isOpenEmbedding_lowerTriangularQuotientMap T (a + d)).isOpenMap.comp
      (lowerTriangularBlockHomeomorph a d F.Carrier).isOpenMap)

/-- The chart is an open map. -/
theorem isOpenMap_lowerBlockQuotientChart (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    IsOpenMap (lowerBlockQuotientChart (a := a) (d := d) (R := F.Carrier)) := by
  let := T.topology
  intro W hW
  have hcover : lowerBlockQuotientChart '' W =
      ⋃ g₀ : GeneralLinear a F.Carrier,
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
theorem isOpenEmbedding_lowerBlockQuotientChart (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    IsOpenEmbedding (lowerBlockQuotientChart (a := a) (d := d) (R := F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact .of_continuous_injective_isOpenMap continuous_lowerBlockQuotientChart
    lowerBlockQuotientChart_injective (isOpenMap_lowerBlockQuotientChart T a d)

/-- The chart is measurable for the Borel structures on the quotients, the
field and the lower triangular group, and the induced product structures. -/
theorem measurable_lowerBlockQuotientChart (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    letI := borel (LeftQuotient (upperUnipotent a F.Carrier))
    letI := borel (LeftQuotient (upperUnipotent (a + d) F.Carrier))
    letI := borel (lowerTriangularSubgroup d F.Carrier)
    Measurable (lowerBlockQuotientChart (a := a) (d := d) (R := F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent a F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent a F.Carrier)) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent (a + d) F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent (a + d) F.Carrier)) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup d F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin d) (Fin a) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin a → F.Carrier))
  have := T.generalLinearSecondCountableTopology d
  have : SecondCountableTopology (lowerTriangularSubgroup d F.Carrier) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact continuous_lowerBlockQuotientChart.measurable

set_option linter.overlappingInstances false in
/-- The range of the chart is conull for every compatible quotient measure: it
contains the conull set of cosets of lower triangular matrices. -/
theorem lowerBlockQuotientChart_range_compl_null (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (GeneralLinear (a + d) F.Carrier)
    letI : BorelSpace (GeneralLinear (a + d) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (a + d) F.Carrier)
    letI : BorelSpace (upperUnipotent (a + d) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (a + d) F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent (a + d) F.Carrier)) := ⟨rfl⟩
    ∀ (μG : Measure (GeneralLinear (a + d) F.Carrier))
      (μH : Measure (upperUnipotent (a + d) F.Carrier))
      [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
      [μH.IsMulRightInvariant] (μ : Measure (LeftQuotient (upperUnipotent (a + d) F.Carrier))),
      IsCompatible (upperUnipotent (a + d) F.Carrier) μG μH μ →
      μ (Set.range (lowerBlockQuotientChart (a := a) (d := d) (R := F.Carrier)))ᶜ = 0 := by
  intro μG μH _ _ _ _ _ μ hμ
  refine measure_mono_null ?_ (padic_lowerTriangular_leftQuotient_conull T (a + d) μG μH μ hμ)
  intro q hq b hb hbq
  exact hq (hbq ▸ mk_lowerTriangular_mem_range_lowerBlockQuotientChart ⟨b, hb⟩)

end Padic

end Langlands.GeneralLinear

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- Proof of `LowerBlockQuotientGeometryStatement`: the actual lower-block chart
is an open measurable embedding with conull range. -/
theorem lowerBlockQuotientGeometry : LowerBlockQuotientGeometryStatement.{uF} := by
  intro p _ F n k
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + k + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
  intro chart _ μ hμ
  exact ⟨isOpenEmbedding_lowerBlockQuotientChart F.canonicalTopologicalData (n + 1) (k + 1),
    measurable_lowerBlockQuotientChart F.canonicalTopologicalData (n + 1) (k + 1),
    lowerBlockQuotientChart_range_compl_null F.canonicalTopologicalData (n + 1) (k + 1)
      (generalLinearHaar F.Carrier (n + 1 + k)) (unipotentHaar F.Carrier (n + 1 + k)) μ hμ⟩

end Langlands.RankinSelberg
