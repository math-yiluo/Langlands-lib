import Langlands.Global.RankinSelberg.EqualAnalyticRowMeasure
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.AdelesLocallyCompactProof
import Langlands.Global.ArchimedeanGL
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # The covolume-one measure on `𝔸^n` as a product measure

Under the splitting `𝔸^n ≅ (F_∞)^n × (𝔸_f)^n`, with `F_∞` the mixed space, the covolume-one
measure `rectangleMeasure F 1 n` is a positive finite multiple of the product of Lebesgue
measure and a Haar measure of `(𝔸_f)^n`. Integrals of tensors therefore factor.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped ENNReal NNReal Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

/-- Shortcut instances for the mixed space; without them instance search fails for powers of
the mixed space. -/
instance mixedSpace_sigmaFinite :
    SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance

instance mixedSpace_isAddHaarMeasure :
    (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance

instance mixedSpace_measurableAdd : MeasurableAdd (mixedEmbedding.mixedSpace F) :=
  inferInstance

instance mixedSpace_borelSpace : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance

instance archRow_borelSpace (n : ℕ) : BorelSpace (Fin n → mixedEmbedding.mixedSpace F) :=
  inferInstance

instance archRow_sigmaFinite (n : ℕ) :
    SigmaFinite (volume : Measure (Fin n → mixedEmbedding.mixedSpace F)) := inferInstance

instance archRow_isAddHaarMeasure (n : ℕ) :
    (volume : Measure (Fin n → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance

local instance productMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance productBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance finiteAdelesMeasurableSpace : MeasurableSpace (FiniteAdeles F) := borel _

local instance finiteAdelesBorelSpace : BorelSpace (FiniteAdeles F) := ⟨rfl⟩

local instance finiteAdelesSecondCountable : SecondCountableTopology (FiniteAdeles F) :=
  finiteAdeles_secondCountableTopology F

local instance finiteAdelesLocallyCompact : LocallyCompactSpace (FiniteAdeles F) :=
  finiteAdeles_locallyCompactSpace F

local instance adelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F

/-- Archimedean row vectors `(F_∞)^n`. -/
abbrev ArchRow (n : ℕ) := Fin n → mixedEmbedding.mixedSpace F

/-- Finite-adelic row vectors `(𝔸_f)^n`. -/
abbrev FinRow (n : ℕ) := Fin n → FiniteAdeles F

/-- The splitting `𝔸^n ≅ (F_∞)^n × (𝔸_f)^n`. -/
def rowSplit (n : ℕ) : RowVector F n ≃ₜ+ ArchRow F n × FinRow F n where
  toFun x := (archimedeanCoordinates F n x, finiteCoordinates F n x)
  invFun p := Matrix.of fun _ j =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 j), p.2 j) : Adeles F)
  left_inv x := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x 0 j).1), (x 0 j).2) : Adeles F) = x 0 j
    rw [RingEquiv.symm_apply_apply]
    rfl
  right_inv p := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => rfl)
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 j)) = p.1 j
    rw [RingEquiv.apply_symm_apply]
  map_add' x y := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => rfl)
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (x 0 j + y 0 j).1 =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (x 0 j).1 +
        InfiniteAdeleRing.ringEquiv_mixedSpace F (y 0 j).1
    exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x 0 j).1 (y 0 j).1
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
    · exact (continuous_infiniteAdeleCoordinates F).comp
        (continuous_fst.comp ((continuous_apply j).comp (continuous_apply 0)))
    · exact continuous_snd.comp ((continuous_apply j).comp (continuous_apply 0))
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Continuous.prodMk
      ((continuous_infiniteAdeleCoordinates_symm F).comp
        ((continuous_apply j).comp continuous_fst))
      ((continuous_apply j).comp continuous_snd)

theorem rowSplit_apply (n : ℕ) (x : RowVector F n) :
    rowSplit F n x = (archimedeanCoordinates F n x, finiteCoordinates F n x) := rfl

/-- The product of Lebesgue measure and a Haar measure of the finite-adelic rows. -/
def rowProductMeasure (n : ℕ) : Measure (ArchRow F n × FinRow F n) :=
  (volume : Measure (ArchRow F n)).prod (Measure.addHaar : Measure (FinRow F n))

instance rowProductMeasure_isAddHaarMeasure (n : ℕ) :
    (rowProductMeasure F n).IsAddHaarMeasure := by
  unfold rowProductMeasure
  infer_instance

variable [CompactSpace (AdeleQuotient F)]

instance map_rowSplit_isAddHaarMeasure (n : ℕ) :
    (Measure.map (rowSplit F n) (rectangleMeasure F 1 n)).IsAddHaarMeasure :=
  (rowSplit F n).toAddEquiv.isAddHaarMeasure_map (rectangleMeasure F 1 n)
    (rowSplit F n).continuous (rowSplit F n).symm.continuous

/-- The scalar relating the covolume-one measure to the product measure. -/
def rowConstant (n : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor (Measure.map (rowSplit F n) (rectangleMeasure F 1 n))
    (rowProductMeasure F n)

theorem map_rowSplit_rectangleMeasure (n : ℕ) :
    Measure.map (rowSplit F n) (rectangleMeasure F 1 n) =
      (rowConstant F n : ℝ≥0∞) • rowProductMeasure F n := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul
    (Measure.map (rowSplit F n) (rectangleMeasure F 1 n)) (rowProductMeasure F n)]
  exact ENNReal.smul_def _ _

theorem rowConstant_ne_zero (n : ℕ) : rowConstant F n ≠ 0 := by
  intro h
  have := map_rowSplit_rectangleMeasure F n
  rw [h, ENNReal.coe_zero, zero_smul] at this
  have hne : Measure.map (rowSplit F n) (rectangleMeasure F 1 n) ≠ 0 := NeZero.ne _
  exact hne this

omit [CompactSpace (AdeleQuotient F)] in
theorem rowSplit_measurableEmbedding (n : ℕ) : MeasurableEmbedding (rowSplit F n) :=
  (rowSplit F n).toHomeomorph.measurableEmbedding

/-- Integrals over `𝔸^n` as integrals for the product measure. -/
theorem integral_rect_eq (n : ℕ) (f : ArchRow F n × FinRow F n → ℂ) :
    ∫ x, f (rowSplit F n x) ∂rectangleMeasure F 1 n =
      (rowConstant F n : ℝ) • ∫ z, f z ∂rowProductMeasure F n := by
  rw [← (rowSplit_measurableEmbedding F n).integral_map, map_rowSplit_rectangleMeasure,
    integral_smul_measure]
  rfl

theorem lintegral_rect_eq (n : ℕ) (f : ArchRow F n × FinRow F n → ℝ≥0∞) :
    ∫⁻ x, f (rowSplit F n x) ∂rectangleMeasure F 1 n =
      (rowConstant F n : ℝ≥0∞) * ∫⁻ z, f z ∂rowProductMeasure F n := by
  rw [← (rowSplit_measurableEmbedding F n).lintegral_map, map_rowSplit_rectangleMeasure,
    lintegral_smul_measure, smul_eq_mul]

theorem integrable_rect_iff (n : ℕ) (f : ArchRow F n × FinRow F n → ℂ) :
    Integrable (fun x => f (rowSplit F n x)) (rectangleMeasure F 1 n) ↔
      Integrable f (rowProductMeasure F n) := by
  change Integrable (f ∘ rowSplit F n) _ ↔ _
  rw [← (rowSplit_measurableEmbedding F n).integrable_map_iff, map_rowSplit_rectangleMeasure]
  exact integrable_smul_measure (ENNReal.coe_ne_zero.mpr (rowConstant_ne_zero F n))
    ENNReal.coe_ne_top

/-- Tensors are integrable when both factors are. -/
theorem integrable_rect_tensor (n : ℕ) {g : ArchRow F n → ℂ} {h : FinRow F n → ℂ}
    (hg : Integrable g) (hh : Integrable h (Measure.addHaar : Measure (FinRow F n))) :
    Integrable (fun x => g (archimedeanCoordinates F n x) * h (finiteCoordinates F n x))
      (rectangleMeasure F 1 n) :=
  (integrable_rect_iff F n (fun z => g z.1 * h z.2)).mpr (hg.mul_prod hh)

/-- Integrals of tensors factor. -/
theorem integral_rect_tensor (n : ℕ) (g : ArchRow F n → ℂ) (h : FinRow F n → ℂ) :
    ∫ x, g (archimedeanCoordinates F n x) * h (finiteCoordinates F n x)
        ∂rectangleMeasure F 1 n =
      (rowConstant F n : ℝ) • ((∫ e, g e) * ∫ a, h a ∂(Measure.addHaar : Measure (FinRow F n))) := by
  have := integral_rect_eq F n (fun z => g z.1 * h z.2)
  rw [rowProductMeasure, integral_prod_mul] at this
  exact this

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
