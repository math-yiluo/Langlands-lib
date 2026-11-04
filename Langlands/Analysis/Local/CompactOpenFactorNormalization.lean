import Langlands.Analysis.Local.QuotientFactorizationHaar

/-! # Explicit Haar normalization on a complementary subgroup -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H K : Subgroup G)
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace K] [BorelSpace K]
  (μG : Measure G) (μH : Measure H) (μK : Measure K)
  (S : OpenSubgroup G) (B : OpenSubgroup K)

/-- The finite real scalar prescribed by the ambient compact-open mass and
the two factor masses. Compactness and positivity are proved below. -/
def compactOpenFactorScalar : ℝ≥0 :=
  (μG (S : Set G)).toNNReal /
    ((μH {h : H | (h : G) ∈ S}).toNNReal * (μK (B : Set K)).toNNReal)

/-- Haar measure on the complement with the local Weil normalization. Its
definition uses the input measures and compact-open subgroups, not a
preselected quotient measure or a desired product-measure identity. -/
def compactOpenFactorMeasure : Measure K :=
  compactOpenFactorScalar H K μG μH μK S B • μK

instance compactOpenFactorMeasure_regular [μK.Regular] :
    (compactOpenFactorMeasure H K μG μH μK S B).Regular := by
  unfold compactOpenFactorMeasure
  infer_instance

instance compactOpenFactorMeasure_isMulRightInvariant [IsMulRightInvariant μK] :
    IsMulRightInvariant (compactOpenFactorMeasure H K μG μH μK S B) := by
  unfold compactOpenFactorMeasure
  infer_instance

instance compactOpenFactorMeasure_sFinite [SFinite μK] :
    SFinite (compactOpenFactorMeasure H K μG μH μK S B) := by
  unfold compactOpenFactorMeasure
  infer_instance

section LocalMass

variable [T2Space G]
  [IsHaarMeasure μG] [IsHaarMeasure μH] [IsHaarMeasure μK]

/-- All three compact-open masses defining the normalization scalar are
strictly positive finite nonnegative reals. -/
theorem compactOpenFactorScalar_pos
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K)) :
    0 < compactOpenFactorScalar H K μG μH μK S B := by
  have hAo : IsOpen {h : H | (h : G) ∈ S} :=
    S.isOpen.preimage continuous_subtype_val
  have hAc : IsCompact {h : H | (h : G) ∈ S} :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  apply div_pos
  · exact ENNReal.toNNReal_pos
      (S.isOpen.measure_pos μG ⟨1, S.one_mem⟩).ne' hS.measure_lt_top.ne
  · exact mul_pos
      (ENNReal.toNNReal_pos (hAo.measure_pos μH ⟨1, S.one_mem⟩).ne'
        hAc.measure_lt_top.ne)
      (ENNReal.toNNReal_pos (B.isOpen.measure_pos μK ⟨1, B.one_mem⟩).ne'
        hB.measure_lt_top.ne)

/-- The explicitly scaled measure satisfies the required local Haar mass
identity. No such identity is assumed. -/
theorem compactOpenFactorMeasure_mass
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K)) :
    μG (S : Set G) = μH {h : H | (h : G) ∈ S} *
      compactOpenFactorMeasure H K μG μH μK S B (B : Set K) := by
  let a := (μH {h : H | (h : G) ∈ S}).toNNReal
  let b := (μK (B : Set K)).toNNReal
  let s := (μG (S : Set G)).toNNReal
  have hAo : IsOpen {h : H | (h : G) ∈ S} :=
    S.isOpen.preimage continuous_subtype_val
  have hAc : IsCompact {h : H | (h : G) ∈ S} :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have ha : a ≠ 0 := (ENNReal.toNNReal_pos
    (hAo.measure_pos μH ⟨1, S.one_mem⟩).ne' hAc.measure_lt_top.ne).ne'
  have hb : b ≠ 0 := (ENNReal.toNNReal_pos
    (B.isOpen.measure_pos μK ⟨1, B.one_mem⟩).ne' hB.measure_lt_top.ne).ne'
  have hnn : s = a * (s / (a * b) * b) := by
    calc
      s = (s / (a * b)) * (a * b) := (div_mul_cancel₀ s (mul_ne_zero ha hb)).symm
      _ = a * (s / (a * b) * b) := mul_left_comm _ _ _
  have he := congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) hnn
  simp only [ENNReal.coe_mul] at he
  rw [compactOpenFactorMeasure, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  simpa only [a, b, s, compactOpenFactorScalar,
    ENNReal.coe_toNNReal hAc.measure_lt_top.ne,
    ENNReal.coe_toNNReal hB.measure_lt_top.ne,
    ENNReal.coe_toNNReal hS.measure_lt_top.ne] using he

/-- The normalized measure is still Haar: the explicit scalar is nonzero. -/
theorem compactOpenFactorMeasure_isHaarMeasure
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K)) :
    IsHaarMeasure (compactOpenFactorMeasure H K μG μH μK S B) :=
  IsHaarMeasure.nnreal_smul μK
    (compactOpenFactorScalar_pos H K μG μH μK S B hH hS hB).ne'

end LocalMass

section Quotient

variable [T2Space G] [LocallyCompactSpace G]
  [IsHaarMeasure μG] [μG.Regular]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]
  (m : H × K ≃ₜ G) (hm : ∀ p : H × K, m p = p.1.val * p.2.val)
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  {ν : Measure (LeftQuotient H)}

/-- Local compact-open geometry suffices for exact normalization of the
actual quotient chart when the complement measure is constructed above. -/
theorem IsCompatible.measurePreserving_compactOpenFactorMeasure
    (hν : IsCompatible H μG μH ν)
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K))
    (horbit : factorQuotientHomeomorph H Subtype.val m hm '' (B : Set K) =
      leftQuotientMap H '' (S : Set G)) :
    MeasurePreserving (factorQuotientHomeomorph H Subtype.val m hm)
      (compactOpenFactorMeasure H K μG μH μK S B) ν := by
  letI := compactOpenFactorMeasure_isHaarMeasure H K μG μH μK S B hH hS hB
  exact hν.measurePreserving_factorQuotientHomeomorph_of_compactOpen H K m hm hH
    (compactOpenFactorMeasure H K μG μH μK S B) S hS B hB horbit
    (compactOpenFactorMeasure_mass H K μG μH μK S B hH hS hB)

/-- The explicit compact-open normalization equals the intrinsic pullback
of any compatible Weil measure. -/
theorem IsCompatible.map_symm_eq_compactOpenFactorMeasure
    (hν : IsCompatible H μG μH ν)
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K))
    (horbit : factorQuotientHomeomorph H Subtype.val m hm '' (B : Set K) =
      leftQuotientMap H '' (S : Set G)) :
    Measure.map (factorQuotientHomeomorph H Subtype.val m hm).symm ν =
      compactOpenFactorMeasure H K μG μH μK S B := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  have hc := hν.measurePreserving_compactOpenFactorMeasure H K μG μH μK S B m hm
    hH hS hB horbit
  rw [← hc.map_eq, Measure.map_map c.symm.continuous.measurable c.continuous.measurable,
    Homeomorph.symm_comp_self, Measure.map_id]

end Quotient

end Langlands.QuotientIntegration
