import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Analysis.Local.QuotientKernelSupport
import Langlands.Group.GL.CountabilityProof
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The actual two-block radical fiber kernel
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration TwoBlockDeformation TwoBlockJacquet
open scoped ENNReal

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The affine radical coordinate change induced by an upper unipotent
matrix preserves the supplied additive Haar measure. -/
theorem map_unipotentShift :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μ.IsAddHaarMeasure] (n : upperUnipotent (t + 1) F.Carrier),
      Measure.map (unipotentShift h n) μ = μ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  intro _ _ μ _ n
  let e := Shahidi.rectangularConj (unipotentLevi h n 0) (unipotentLevi h n 1)
  let a : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier :=
    ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * unipotentCorner h n
  have hμ : μ.map e = μ := by
    simpa only [determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 0),
      determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 1),
      Units.val_one, one_pow, div_one, one_smul] using
      Shahidi.map_rectangularConj_padic F T μ (unipotentLevi h n 0) (unipotentLevi h n 1)
  have hshift : unipotentShift h n = (fun x => a + x) ∘ e := by
    funext x
    simp only [Function.comp_apply, unipotentShift, e, Shahidi.rectangularConj_apply, a]
    rw [Matrix.mul_add, Matrix.mul_assoc]
  rw [hshift, ← Measure.map_map (measurable_const_add a) e.measurable, hμ,
    map_add_left_eq_self]

/-- Joint measurability makes the representative fiber measures measurable
as a map from the ambient group to the space of measures. -/
theorem measurable_fiberMeasures :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
      [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [SFinite μ],
      Measurable (fun g => Measure.map (fun x => fiberPoint h F.Carrier x g) μ) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.secondCountableTopology
  let := T.generalLinearSecondCountableTopology (t + 1)
  intro _ _ _ _ _ _ μ _
  have hf := (continuous_fiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μ))
  simpa only [Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

/-- The representative fiber measures are invariant under changing the
representative by left multiplication from the full unipotent subgroup. -/
theorem fiberMeasures_upperUnipotent_mul :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μ.IsAddHaarMeasure] (n : upperUnipotent (t + 1) F.Carrier)
      (g : GeneralLinear (t + 1) F.Carrier),
      Measure.map (fun x => fiberPoint h F.Carrier x (n.val * g)) μ =
        Measure.map (fun x => fiberPoint h F.Carrier x g) μ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.secondCountableTopology
  intro _ _ _ _ μ _ n g
  have hshift : Measurable (unipotentShift h n) := by
    let := T.valuativeRel
    let := T.localField
    have hs : Continuous (unipotentShift h n) := continuous_const.matrix_mul
      (continuous_const.add (continuous_id.matrix_mul continuous_const))
    exact hs.measurable
  have hf : Measurable (fun x => fiberPoint h F.Carrier x g) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  simp only [fiberPoint_upperUnipotent_mul]
  change Measure.map ((fun x => fiberPoint h F.Carrier x g) ∘ unipotentShift h n) μ = _
  rw [← Measure.map_map hf hshift, map_unipotentShift F h μ n]

/-- The actual descended measure kernel. Its value is the prescribed
pushforward of the supplied radical measure, without normalization. -/
def fiberKernel :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
      [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
      [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μ.IsAddHaarMeasure],
      Kernel (LeftUnipotentQuotient t F.Carrier) (BlockQuotient h F.Carrier) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  intro _ _ _ _ _ _ _ _ μ _
  let : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  let : SecondCountableTopology (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  let k := descend (upperUnipotent (t + 1) F.Carrier)
    (fun g => Measure.map (fun x => fiberPoint h F.Carrier x g) μ)
    (fiberMeasures_upperUnipotent_mul F h μ)
  refine ⟨k, (measurable_quotient_iff _ (UpperUnipotent.isClosed (R := F.Carrier)) k).2 ?_⟩
  exact measurable_fiberMeasures F h μ

/-- Representative evaluation of the descended kernel is exact. -/
theorem fiberKernel_mk :
    letI := F.canonicalTopologicalData.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
      [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
      [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
      [MeasurableSpace (BlockQuotient h F.Carrier)] [BorelSpace (BlockQuotient h F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
      [μ.IsAddHaarMeasure] (g : GeneralLinear (t + 1) F.Carrier),
      fiberKernel F h μ (Quotient.mk _ g) =
        Measure.map (fun x => fiberPoint h F.Carrier x g) μ := by
  let := F.canonicalTopologicalData.topology
  intro _ _ _ _ _ _ _ _ μ _ g
  rfl

end Langlands.RankinSelberg.TwoBlockUnipotentQuotient
