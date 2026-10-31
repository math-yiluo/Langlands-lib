import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.BlockUnipotentCoordinates
import Langlands.HarmonicAnalysis.TriangularTranslationProof
import Langlands.HarmonicAnalysis.RowFourier
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Actual scalar entry coordinates and Haar measure on the upper unipotent group. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal

namespace Langlands.GeneralLinear

open BlockShape HarmonicAnalysis

universe uK

/-- Strictly upper entry positions of a square matrix. -/
abbrev UpperEntryPair (d : ℕ) := (singletons d).UpperPair

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

private def oneEntryHomeomorph : Matrix (Fin 1) (Fin 1) K ≃ₜ K :=
  (Homeomorph.piUnique (fun _ : Fin 1 => Fin 1 → K)).trans
    (Homeomorph.piUnique (fun _ : Fin 1 => K))

/-- The actual strictly upper entries, with inverse the upper unipotent matrix
having these entries. This is a homeomorphism of spaces, not a group map to the
pointwise additive coordinate group. -/
def upperEntryCoordinates (d : ℕ) :
    upperUnipotent d K ≃ₜ (UpperEntryPair d → K) :=
  (((upperUnipotentContinuousEquivRadical (n := d) K).toHomeomorph).trans
    ((singletons d).radicalCoordinatesHomeomorph K)).trans
    (Homeomorph.piCongrRight fun _ => oneEntryHomeomorph (K := K))

@[simp] theorem upperEntryCoordinates_apply {d : ℕ}
    (u : upperUnipotent d K) (ij : UpperEntryPair d) :
    upperEntryCoordinates d u ij = u.val.val ij.1.1 ij.1.2 := by
  change u.val.val ((singletons d).index ij.1.1 0)
    ((singletons d).index ij.1.2 0) = _
  simp only [singletons_index (n := d)]

@[simp] theorem upperEntryCoordinates_symm_upper {d : ℕ}
    (X : UpperEntryPair d → K) {i j : Fin d} (hij : i < j) :
    ((upperEntryCoordinates d (K := K)).symm X).val.val i j = X ⟨(i, j), hij⟩ := by
  simpa only [upperEntryCoordinates_apply] using
    congrFun ((upperEntryCoordinates d (K := K)).apply_symm_apply X) ⟨(i, j), hij⟩

/-- Scalar entry form of the published triangular block multiplication law. -/
theorem upperEntryCoordinates_mul {d : ℕ} (u v : upperUnipotent d K)
    (ij : UpperEntryPair d) :
    upperEntryCoordinates d (u * v) ij =
      upperEntryCoordinates d u ij + upperEntryCoordinates d v ij +
        ∑ k : {k : Fin d // ij.1.1 < k ∧ k < ij.1.2},
          upperEntryCoordinates d u ⟨(ij.1.1, k), k.2.1⟩ *
            upperEntryCoordinates d v ⟨(k, ij.1.2), k.2.2⟩ := by
  have h := (singletons d).radicalCoordinates_mul K
    (upperUnipotentEquivRadical K u) (upperUnipotentEquivRadical K v) ij.2
  rw [← map_mul] at h
  have h00 := congrFun (congrFun h 0) 0
  simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply,
    Fin.sum_univ_one, radicalCoordinates_apply, singletons_index (n := d),
    upperUnipotentEquivRadical_apply_val, upperEntryCoordinates_apply] using h00

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- The product of the supplied scalar Haar measure on the strictly upper entries. -/
def upperEntryProductMeasure (ν : AdditiveHaarMeasure K) (d : ℕ) :
    Measure (UpperEntryPair d → K) := Measure.pi (fun _ => ν.measure)

instance upperEntryProductMeasure_sigmaFinite (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (d : ℕ) : SigmaFinite (upperEntryProductMeasure ν d) :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun _ : UpperEntryPair d => ν.measure)))

instance upperEntryProductMeasure_isAddHaar (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (d : ℕ) : (upperEntryProductMeasure ν d).IsAddHaarMeasure :=
  inferInstanceAs (Measure.pi (fun _ : UpperEntryPair d => ν.measure)).IsAddHaarMeasure

omit [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
private theorem coordinateCorrection_depends {d : ℕ} (a : upperUnipotent d K)
    (ij : UpperEntryPair d) (X Y : UpperEntryPair d → K)
    (h : ∀ kl : UpperEntryPair d,
      kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → X kl = Y kl) :
    (upperEntryCoordinates d (a * (upperEntryCoordinates d).symm X) - X) ij =
      (upperEntryCoordinates d (a * (upperEntryCoordinates d).symm Y) - Y) ij := by
  simp only [Pi.sub_apply, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
  have hs :
      (∑ k : {k : Fin d // ij.1.1 < k ∧ k < ij.1.2},
        upperEntryCoordinates d a ⟨(ij.1.1, k), k.2.1⟩ * X ⟨(k, ij.1.2), k.2.2⟩) =
      ∑ k : {k : Fin d // ij.1.1 < k ∧ k < ij.1.2},
        upperEntryCoordinates d a ⟨(ij.1.1, k), k.2.1⟩ * Y ⟨(k, ij.1.2), k.2.2⟩ := by
    apply Finset.sum_congr rfl
    intro k _
    rw [h ⟨(k, ij.1.2), k.2.2⟩]
    have hi : ij.1.1.val < k.val.val := k.2.1
    have hj : k.val.val < ij.1.2.val := k.2.2
    dsimp
    omega
  rw [hs]
  abel

/-- In scalar entry coordinates, left upper-unipotent multiplication preserves
the product of the supplied scalar Haar measures. -/
theorem upperEntry_leftTranslation_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (d : ℕ) (a : upperUnipotent d K) :
    MeasurePreserving
      (fun X => upperEntryCoordinates d (a * (upperEntryCoordinates d).symm X))
      (upperEntryProductMeasure ν d) (upperEntryProductMeasure ν d) := by
  let f : (UpperEntryPair d → K) → UpperEntryPair d → K :=
    fun X => upperEntryCoordinates d (a * (upperEntryCoordinates d).symm X) - X
  have hf : Continuous f :=
    ((upperEntryCoordinates d).continuous.comp
      (continuous_const.mul (upperEntryCoordinates d).symm.continuous)).sub continuous_id
  have hp := finiteTriangularTranslation (UpperEntryPair d) (fun _ => K)
    (fun _ => ν.measure) (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable
    (coordinateCorrection_depends a)
  have he : (fun X ij => f X ij + X ij) =
      fun X => upperEntryCoordinates d (a * (upperEntryCoordinates d).symm X) := by
    funext X ij
    exact sub_add_cancel _ _
  rw [he] at hp
  exact hp

variable {d : ℕ} [MeasurableSpace (upperUnipotent d K)]
  [BorelSpace (upperUnipotent d K)]

/-- Transporting the supplied scalar product measure through the actual entry
coordinates gives a Haar measure on the actual upper-unipotent group. -/
theorem upperEntryProductMeasure_isHaar (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] :
    ((upperEntryProductMeasure ν d).map (upperEntryCoordinates d).symm).IsHaarMeasure := by
  let e := upperEntryCoordinates d (K := K)
  have he : Measurable e.symm := e.symm.measurable
  have : IsFiniteMeasureOnCompacts ((upperEntryProductMeasure ν d).map e.symm) :=
    IsFiniteMeasureOnCompacts.map (upperEntryProductMeasure ν d) e.symm
  have : IsOpenPosMeasure ((upperEntryProductMeasure ν d).map e.symm) :=
    e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  refine { map_mul_left_eq_self := fun a => ?_ }
  have hp := upperEntry_leftTranslation_preserving ν d a
  have hm : Measurable (fun u : upperUnipotent d K => a * u) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hm he]
  have heq : (fun u : upperUnipotent d K => a * u) ∘ e.symm =
      e.symm ∘ (fun X => e (a * e.symm X)) := by
    funext X
    simp
  rw [heq, ← Measure.map_map he hp.measurable, hp.map_eq]

variable [LocallyCompactSpace K]

/-- Every actual upper-unipotent Haar measure differs from the entry product
by one positive real factor, retained explicitly in the integral formula. -/
theorem exists_upperEntry_integral (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (μ : Measure (upperUnipotent d K)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : upperUnipotent d K → ℂ,
      (∫ u, f u ∂μ) = (c : ℂ) * ∫ X, f ((upperEntryCoordinates d).symm X)
        ∂upperEntryProductMeasure ν d := by
  let e := upperEntryCoordinates d (K := K)
  let μcoord := (upperEntryProductMeasure ν d).map e.symm
  let : μcoord.IsHaarMeasure := upperEntryProductMeasure_isHaar ν
  let : LocallyCompactSpace (upperUnipotent d K) := e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology (upperUnipotent d K) := e.secondCountableTopology
  let c := haarScalarFactor μ μcoord
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure μ μcoord
  have hμ : μ = c • μcoord := isMulLeftInvariant_eq_smul μ μcoord
  refine ⟨c, hc, fun f => ?_⟩
  rw [hμ, integral_smul_nnreal_measure]
  change c • (∫ u, f u ∂(upperEntryProductMeasure ν d).map e.symm) = _
  rw [e.symm.isClosedEmbedding.integral_map f]
  simp only [NNReal.smul_def, Complex.real_smul]
  rfl

end Langlands.GeneralLinear
