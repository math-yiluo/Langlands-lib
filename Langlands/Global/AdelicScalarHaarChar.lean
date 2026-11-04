import Langlands.Global.PositiveRealIdeles
import Langlands.Global.ArchimedeanGL
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.AdelesLocallyCompactProof
import Langlands.HarmonicAnalysis.TriangularHaarModulus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Haar scaling of the adeles by positive real ideles

Multiplication by the idele `full F σ` (the positive real `σ` at every infinite place and `1`
at every finite place) scales additive Haar measure on `𝔸_F` by `σ ^ [F : ℚ]`. The paired
Markdown records the argument.
-/

noncomputable section

universe uF

namespace Langlands.Global.PositiveRealIdeles

open MeasureTheory MeasureTheory.Measure
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NNReal ENNReal

variable (F : Type uF) [Field F] [NumberField F]

omit [NumberField F] in
/-- In mixed coordinates, multiplication by the positive real infinite idele `σ` is the real
scalar multiplication by `σ`. -/
theorem ringEquiv_mixedSpace_infinite_mul (σ : ℝ≥0ˣ) (x : InfiniteAdeles F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F ((infinite F σ : InfiniteAdeles F) * x) =
      ((σ : ℝ≥0) : ℝ) • InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
  rw [map_mul]
  ext v
  · change extensionEmbeddingOfIsReal v.2 (realEmbedding F v.1 ((σ : ℝ≥0) : ℝ)) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 v = _
    have h : extensionEmbeddingOfIsReal v.2 (realEmbedding F v.1 ((σ : ℝ≥0) : ℝ)) =
        ((σ : ℝ≥0) : ℝ) := by
      apply Complex.ofReal_injective
      rw [extensionEmbeddingOfIsReal_apply, extensionEmbedding_realEmbedding]
    rw [h]
    rfl
  · change extensionEmbedding v.1 (realEmbedding F v.1 ((σ : ℝ≥0) : ℝ)) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 v = _
    rw [extensionEmbedding_realEmbedding]
    simp [Complex.real_smul]

open scoped Classical in
/-- The infinite adeles carry the image of the mixed-space volume as an additive Haar measure,
and multiplication by the positive real infinite idele `σ` scales it by `σ ^ [F : ℚ]`. -/
theorem map_infinite_mul_volume [MeasurableSpace (InfiniteAdeles F)]
    [BorelSpace (InfiniteAdeles F)] (σ : ℝ≥0ˣ) :
    ((σ : ℝ≥0) ^ Module.finrank ℚ F) •
        (((volume : Measure (mixedEmbedding.mixedSpace F)).map
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm).map
            fun x => (infinite F σ : InfiniteAdeles F) * x) =
      (volume : Measure (mixedEmbedding.mixedSpace F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hRs : Measurable R.symm := (continuous_infiniteAdeleCoordinates_symm F).measurable
  have hmul : Measurable fun x : InfiniteAdeles F => (infinite F σ : InfiniteAdeles F) * x :=
    (continuous_const.mul continuous_id).measurable
  have hσ : ((σ : ℝ≥0) : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr σ.ne_zero
  have hcomp : (fun x : InfiniteAdeles F => (infinite F σ : InfiniteAdeles F) * x) ∘ R.symm =
      R.symm ∘ fun y => ((σ : ℝ≥0) : ℝ) • y := by
    funext y
    apply R.injective
    change R ((infinite F σ : InfiniteAdeles F) * R.symm y) = R (R.symm (((σ : ℝ≥0) : ℝ) • y))
    rw [R.apply_symm_apply]
    exact (ringEquiv_mixedSpace_infinite_mul F σ (R.symm y)).trans
      (congrArg (((σ : ℝ≥0) : ℝ) • ·) (R.apply_symm_apply y))
  rw [Measure.map_map hmul hRs, hcomp, ← Measure.map_map hRs (measurable_const_smul _),
    Measure.map_addHaar_smul _ hσ, Measure.map_smul _ hRs.aemeasurable, ← smul_assoc,
    mixedEmbedding.finrank]
  have hpos : (0 : ℝ) < ((σ : ℝ≥0) : ℝ) ^ Module.finrank ℚ F :=
    pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) hσ.symm) _
  have hc : ((σ : ℝ≥0) ^ Module.finrank ℚ F : ℝ≥0) •
      ENNReal.ofReal |(((σ : ℝ≥0) : ℝ) ^ Module.finrank ℚ F)⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.mpr hpos), ← NNReal.coe_pow, ← NNReal.coe_inv,
      ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_mul,
      mul_inv_cancel₀ (pow_ne_zero _ σ.ne_zero), ENNReal.coe_one]
  rw [hc, one_smul]

/-- **Haar scaling by positive real ideles.** For every Borel structure on `𝔸_F`, the additive
Haar character of multiplication by the idele `full F σ` is `σ ^ [F : ℚ]`. -/
theorem addEquivAddHaarChar_mulLeft_full [MeasurableSpace (Adeles F)] [BorelSpace (Adeles F)]
    (σ : ℝ≥0ˣ) :
    letI := adeles_locallyCompactSpace F
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (full F σ)) =
      (σ : ℝ≥0) ^ Module.finrank ℚ F := by
  classical
  let := adeles_locallyCompactSpace F
  let : MeasurableSpace (InfiniteAdeles F) := borel _
  have : BorelSpace (InfiniteAdeles F) := ⟨rfl⟩
  let : MeasurableSpace (FiniteAdeles F) := borel _
  have : BorelSpace (FiniteAdeles F) := ⟨rfl⟩
  have := infiniteAdeles_secondCountableTopology F
  have := finiteAdeles_secondCountableTopology F
  have := finiteAdeles_locallyCompactSpace F
  have := adeles_secondCountableTopology F
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F
  -- the two factor measures
  let μi : Measure (InfiniteAdeles F) := (volume : Measure (mixedEmbedding.mixedSpace F)).map R.symm
  have : IsAddHaarMeasure μi :=
    R.symm.toAddEquiv.isAddHaarMeasure_map volume (continuous_infiniteAdeleCoordinates_symm F)
      (continuous_infiniteAdeleCoordinates F)
  let μf : Measure (FiniteAdeles F) := addHaar
  -- the adeles as the product of their infinite and finite parts
  let e : (InfiniteAdeles F × FiniteAdeles F) ≃ₜ+ Adeles F :=
    { toFun := fun p => p
      invFun := fun p => p
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  have he : Measurable e := e.continuous.measurable
  let μ : Measure (Adeles F) := (μi.prod μf).map e
  have : IsAddHaarMeasure μ := e.isAddHaarMeasure_map _
  have : Regular μ := by
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Adeles F)) := inferInstance
    exact regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  apply Langlands.HarmonicAnalysis.addEquivAddHaarChar_eq_of_smul_map μ
  -- multiplication by `full F σ` is multiplication by `σ` on the infinite factor
  let f : InfiniteAdeles F → InfiniteAdeles F := fun x => (infinite F σ : InfiniteAdeles F) * x
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have hφ : Measurable (ContinuousAddEquiv.mulLeft (full F σ)) :=
    (ContinuousAddEquiv.mulLeft (full F σ)).continuous.measurable
  have hcomp : (ContinuousAddEquiv.mulLeft (full F σ) : Adeles F → Adeles F) ∘ e =
      e ∘ Prod.map f id := by
    funext p
    change ((f p.1, 1 * p.2) : InfiniteAdeles F × FiniteAdeles F) = (f p.1, p.2)
    rw [one_mul]
  change ((σ : ℝ≥0) ^ Module.finrank ℚ F) •
      Measure.map (ContinuousAddEquiv.mulLeft (full F σ)) ((μi.prod μf).map e) =
    (μi.prod μf).map e
  rw [Measure.map_map hφ he, hcomp, ← Measure.map_map he (hf.prodMap measurable_id),
    ← Measure.map_prod_map μi μf hf measurable_id, Measure.map_id, ← Measure.map_smul _ he.aemeasurable,
    ← Measure.prod_smul_left]
  congr 2
  exact map_infinite_mul_volume F σ

end Langlands.Global.PositiveRealIdeles
