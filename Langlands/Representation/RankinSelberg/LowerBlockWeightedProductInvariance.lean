import Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.MeasureTheory.Group.Prod

/-!
# Invariance of the determinant-weighted lower-block product

The exact determinant density on the small lower triangular group cancels
the determinant scaling of its right action on the rectangular coordinate.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis GeneralLinear
open scoped ENNReal NNReal

universe uF

private theorem map_withDensity_equiv_of_preserving
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (e : A ≃ᵐ A)
    (he : MeasurePreserving e μ μ) (w : A → ℝ≥0∞) :
    Measure.map e (μ.withDensity w) = μ.withDensity (w ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage_emb e.measurableEmbedding (w ∘ e.symm) s

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The representative density `|det b|^(-d)` on the actual small lower
triangular group. It is the pullback of the published quotient density. -/
def lowerTriangularBlockDensity (T : F.TopologicalData) (a d : ℕ)
    (b : lowerTriangularSubgroup a F.Carrier) : ℝ≥0∞ :=
  ENNReal.ofReal (T.normalizedAbs (Matrix.det b.val.val)) ^ (-(d : ℤ))

theorem lowerTriangularBlockDensity_eq_coe (T : F.TopologicalData) (a d : ℕ)
    (b : lowerTriangularSubgroup a F.Carrier) :
    lowerTriangularBlockDensity T a d b =
      (((T.determinantNorm a b.val : ℝ≥0) ^ (-(d : ℤ)) : ℝ≥0) : ℝ≥0∞) := by
  rw [lowerTriangularBlockDensity,
    ENNReal.coe_zpow (T.determinantNorm a b.val).ne_zero]
  congr 1
  exact ENNReal.ofReal_coe_nnreal (p := (T.determinantNorm a b.val : ℝ≥0))

theorem continuous_lowerTriangularBlockDensity (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    Continuous (lowerTriangularBlockDensity T a d) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (continuous_lowerBlockQuotientDensity T a d).comp
    ((Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap _).continuous.comp
      continuous_subtype_val)

/-- Right translation of the weighted triangular factor has exactly the
positive determinant multiplier that cancels rectangular right scaling. -/
theorem map_lowerTriangularBlockDensity_mulRight (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (lowerTriangularSubgroup a F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup a F.Carrier)]
      (ρ : Measure (lowerTriangularSubgroup a F.Carrier)) [ρ.IsMulRightInvariant]
      (g : lowerTriangularSubgroup a F.Carrier),
      Measure.map (fun b => b * g) (ρ.withDensity (lowerTriangularBlockDensity T a d)) =
        ((T.determinantNorm a g.val : ℝ≥0) ^ d) •
          ρ.withDensity (lowerTriangularBlockDensity T a d) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ ρ _ g
  have hw : Measurable (lowerTriangularBlockDensity T a d) :=
    (continuous_lowerTriangularBlockDensity T a d).measurable
  change Measure.map (MeasurableEquiv.mulRight g)
    (ρ.withDensity (lowerTriangularBlockDensity T a d)) = _
  rw [map_withDensity_equiv_of_preserving ρ (MeasurableEquiv.mulRight g)
    (measurePreserving_mul_right ρ g)]
  have hweight : lowerTriangularBlockDensity T a d ∘ (MeasurableEquiv.mulRight g).symm =
      (((T.determinantNorm a g.val : ℝ≥0) ^ d : ℝ≥0) : ℝ≥0∞) •
        lowerTriangularBlockDensity T a d := by
    funext b
    change lowerTriangularBlockDensity T a d (b * g⁻¹) = _ *
      lowerTriangularBlockDensity T a d b
    rw [lowerTriangularBlockDensity_eq_coe, lowerTriangularBlockDensity_eq_coe]
    rw [← ENNReal.coe_mul]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, zpow_neg, zpow_natCast, mul_pow, mul_inv_rev,
      inv_pow, inv_inv]
  rw [hweight, withDensity_smul _ hw]
  rfl

/-- The rectangular additive factor scales by the inverse determinant
multiplier under right multiplication by the small block. -/
theorem map_rectangularMeasure_mulRight (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ (η : AdditiveHaarMeasure F.Carrier) (g : Langlands.GeneralLinear a F.Carrier),
      Measure.map (fun X : Matrix (Fin d) (Fin a) F.Carrier => X * g.val)
        (rectangularMeasure η d a) =
        ((T.determinantNorm a g : ℝ≥0) ^ d)⁻¹ • rectangularMeasure η d a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro η g
  simpa only [inv_inv, Units.val_one, Matrix.one_mul, map_one, Units.val_one, one_pow,
    map_inv, Units.val_inv_eq_inv_val, inv_pow, one_div, inv_inv] using
    padicRectangularHaarScaling F T d a (rectangularMeasure η d a) 1 g⁻¹

/-- Simultaneous right translation of the two triangular factors and right
linear change of the rectangular coordinate preserves the weighted product. -/
theorem measurePreserving_lowerBlockWeightedProduct_diagonal
    (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ [MeasurableSpace (lowerTriangularSubgroup a F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup a F.Carrier)]
      [MeasurableSpace (lowerTriangularSubgroup d F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup d F.Carrier)]
      (η : AdditiveHaarMeasure F.Carrier)
      (ρa : Measure (lowerTriangularSubgroup a F.Carrier)) [SFinite ρa]
      [ρa.IsMulRightInvariant]
      (ρd : Measure (lowerTriangularSubgroup d F.Carrier)) [SFinite ρd]
      [ρd.IsMulRightInvariant]
      (g : lowerTriangularSubgroup a F.Carrier)
      (h : lowerTriangularSubgroup d F.Carrier),
      MeasurePreserving
        (fun z : lowerTriangularSubgroup a F.Carrier ×
            Matrix (Fin d) (Fin a) F.Carrier × lowerTriangularSubgroup d F.Carrier =>
          (z.1 * g, z.2.1 * g.val.val, z.2.2 * h))
        ((ρa.withDensity (lowerTriangularBlockDensity T a d)).prod
          ((rectangularMeasure η d a).prod ρd))
        ((ρa.withDensity (lowerTriangularBlockDensity T a d)).prod
          ((rectangularMeasure η d a).prod ρd)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro _ _ _ _ η ρa _ _ ρd _ _ g h
  have hXm : Measurable (fun X : Matrix (Fin d) (Fin a) F.Carrier =>
      X * g.val.val) := (continuous_id.matrix_mul continuous_const).measurable
  change MeasurePreserving
    (Prod.map (fun b => b * g) (Prod.map (fun X => X * g.val.val) (fun b => b * h))) _ _
  refine ⟨(measurable_mul_const g).prodMap (hXm.prodMap (measurable_mul_const h)), ?_⟩
  rw [← map_prod_map _ _ (measurable_mul_const g)
      (hXm.prodMap (measurable_mul_const h)),
    ← map_prod_map _ _ hXm (measurable_mul_const h),
    map_lowerTriangularBlockDensity_mulRight T a d,
    map_rectangularMeasure_mulRight T a d,
    map_mul_right_eq_self]
  rw [prod_smul_left, prod_smul_left, prod_smul_right, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero d (T.determinantNorm a g.val).ne_zero), one_smul]

/-- A triangular-dependent additive translation of the rectangular factor
preserves the weighted product. -/
theorem measurePreserving_lowerBlockWeightedProduct_shear
    (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ [MeasurableSpace (lowerTriangularSubgroup a F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup a F.Carrier)]
      [MeasurableSpace (lowerTriangularSubgroup d F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup d F.Carrier)]
      (η : AdditiveHaarMeasure F.Carrier)
      (ρa : Measure (lowerTriangularSubgroup a F.Carrier)) [SFinite ρa]
      (ρd : Measure (lowerTriangularSubgroup d F.Carrier)) [SFinite ρd]
      (y : Matrix (Fin d) (Fin a) F.Carrier),
      MeasurePreserving
        (fun z : lowerTriangularSubgroup a F.Carrier ×
            Matrix (Fin d) (Fin a) F.Carrier × lowerTriangularSubgroup d F.Carrier =>
          (z.1, z.2.1 + z.2.2.val.val * y, z.2.2))
        ((ρa.withDensity (lowerTriangularBlockDensity T a d)).prod
          ((rectangularMeasure η d a).prod ρd))
        ((ρa.withDensity (lowerTriangularBlockDensity T a d)).prod
          ((rectangularMeasure η d a).prod ρd)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro _ _ _ _ η ρa _ ρd _ y
  let := T.generalLinearSecondCountableTopology d
  have : SecondCountableTopology (lowerTriangularSubgroup d F.Carrier) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have hsm : Measurable
      (Function.uncurry fun (b : lowerTriangularSubgroup d F.Carrier)
        (X : Matrix (Fin d) (Fin a) F.Carrier) => X + b.val.val * y) :=
    (continuous_snd.add
      ((Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_mul
        continuous_const)).measurable
  have hs := (MeasurePreserving.id ρd).skew_product hsm
    (Filter.Eventually.of_forall fun b =>
      (measurePreserving_add_right (rectangularMeasure η d a) (b.val.val * y)).map_eq)
  have hs' : MeasurePreserving
      (fun z : Matrix (Fin d) (Fin a) F.Carrier × lowerTriangularSubgroup d F.Carrier =>
        (z.1 + z.2.val.val * y, z.2))
      ((rectangularMeasure η d a).prod ρd)
      ((rectangularMeasure η d a).prod ρd) :=
    measurePreserving_swap.comp (hs.comp measurePreserving_swap)
  exact (MeasurePreserving.id _).prod hs'

/-- The actual lower-block right multiplication in parameter coordinates
preserves the determinant-weighted right-associated product measure. -/
theorem measurePreserving_lowerBlockWeightedProduct_mulRight
    (T : F.TopologicalData) (a d : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ [MeasurableSpace (lowerTriangularSubgroup a F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup a F.Carrier)]
      [MeasurableSpace (lowerTriangularSubgroup d F.Carrier)]
      [BorelSpace (lowerTriangularSubgroup d F.Carrier)]
      (η : AdditiveHaarMeasure F.Carrier)
      (ρa : Measure (lowerTriangularSubgroup a F.Carrier)) [SFinite ρa]
      [ρa.IsMulRightInvariant]
      (ρd : Measure (lowerTriangularSubgroup d F.Carrier)) [SFinite ρd]
      [ρd.IsMulRightInvariant]
      (g : lowerTriangularSubgroup a F.Carrier)
      (y : Matrix (Fin d) (Fin a) F.Carrier)
      (h : lowerTriangularSubgroup d F.Carrier),
      MeasurePreserving
        (fun z : lowerTriangularSubgroup a F.Carrier ×
            Matrix (Fin d) (Fin a) F.Carrier × lowerTriangularSubgroup d F.Carrier =>
          (z.1 * g, z.2.1 * g.val.val + z.2.2.val.val * y, z.2.2 * h))
        ((ρa.withDensity (lowerTriangularBlockDensity T a d)).prod
          ((rectangularMeasure η d a).prod ρd))
        ((ρa.withDensity (lowerTriangularBlockDensity T a d)).prod
          ((rectangularMeasure η d a).prod ρd)) := by
  let := T.topology
  let := borel F.Carrier
  intro _ _ _ _ η ρa _ _ ρd _ _ g y h
  convert (measurePreserving_lowerBlockWeightedProduct_diagonal T a d η ρa ρd g h).comp
    (measurePreserving_lowerBlockWeightedProduct_shear T a d η ρa ρd (y * g.val.inv))
    using 1
  funext z
  simp only [Function.comp_apply, Matrix.add_mul, Matrix.mul_assoc,
    g.val.inv_val, Matrix.mul_one]

end Langlands.RankinSelberg
