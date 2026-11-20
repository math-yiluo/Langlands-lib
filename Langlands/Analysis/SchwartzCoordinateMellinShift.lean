import Langlands.Analysis.SchwartzPositiveMellin

/-! # Coordinate integration by parts on the positive orthant -/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators LineDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "R" => ι → ℝ
private abbrev ComplementCoordinates (i : ι) := {j : ι // j ≠ i} → ℝ

private def insertCoordinate (i : ι) : (ComplementCoordinates i × ℝ) ≃ᵐ R :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option {j // j ≠ i} => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe i))

omit [Fintype ι] in
private theorem insertCoordinate_same (i : ι) (x : ComplementCoordinates i) (t : ℝ) :
    insertCoordinate i (x, t) i = t := by
  change (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe i))
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option {j // j ≠ i} => ℝ)).symm (x, t))
    (Equiv.optionSubtypeNe i none) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

omit [Fintype ι] in
private theorem insertCoordinate_other (i : ι) (x : ComplementCoordinates i) (t : ℝ) (j : {j : ι // j ≠ i}) :
    insertCoordinate i (x, t) j.val = x j := by
  change (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Equiv.optionSubtypeNe i))
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option {j // j ≠ i} => ℝ)).symm (x, t))
    (Equiv.optionSubtypeNe i (some j)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

private theorem measurePreserving_insertCoordinate (i : ι) :
    MeasurePreserving (insertCoordinate i)
      ((positiveCoordinateMeasure {j // j ≠ i}).prod positiveLineMeasure)
      (positiveCoordinateMeasure ι) :=
  (measurePreserving_piCongrLeft (fun _ : ι => positiveLineMeasure) (Equiv.optionSubtypeNe i)).comp
    ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option {j // j ≠ i} => ℝ)).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ : Option {j // j ≠ i} => positiveLineMeasure)⟩

private def singleCoordinate (i : ι) : ℝ →ₗᵢ[ℝ] R :=
  LinearIsometry.single ℝ (fun _ : ι => ℝ) i

private theorem insertCoordinate_eq (i : ι) (y : ComplementCoordinates i) (t : ℝ) :
    insertCoordinate i (y, t) = singleCoordinate i t + insertCoordinate i (y, 0) := by
  funext j
  change insertCoordinate i (y, t) j = (Pi.single i t : R) j + insertCoordinate i (y, 0) j
  rcases eq_or_ne j i with rfl | hj
  · simp only [insertCoordinate_same, Pi.single_eq_same, add_zero]
  · have h₁ := insertCoordinate_other i y t ⟨j, hj⟩
    have h₀ := insertCoordinate_other i y 0 ⟨j, hj⟩
    rw [h₁, h₀, Pi.single_eq_of_ne hj, zero_add]

private def coordinateSlice (Φ : SchwartzMap R ℂ) (i : ι) (y : ComplementCoordinates i) :
    SchwartzMap ℝ ℂ := by
  have h : Isometry (fun t : ℝ => singleCoordinate i t + insertCoordinate i (y, 0)) :=
    (isometry_add_right (insertCoordinate i (y, 0))).comp (singleCoordinate i).isometry
  exact SchwartzMap.compCLMOfAntilipschitz ℂ
    ((singleCoordinate i).toContinuousLinearMap.hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const (insertCoordinate i (y, 0)))) h.antilipschitzWith Φ

private theorem coordinateSlice_apply (Φ : SchwartzMap R ℂ) (i : ι) (y : ComplementCoordinates i) (t : ℝ) :
    coordinateSlice Φ i y t = Φ (insertCoordinate i (y, t)) := by
  change Φ (singleCoordinate i t + insertCoordinate i (y, 0)) = _
  rw [← insertCoordinate_eq]

/-- Partial derivative in one real coordinate of a Schwartz test. -/
def schwartzCoordinateDeriv (i : ι) (Φ : SchwartzMap R ℂ) : SchwartzMap R ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap R ℂ) (Pi.single i 1 : R) Φ

private theorem coordinateSlice_deriv (i : ι) (Φ : SchwartzMap R ℂ) (y : ComplementCoordinates i) :
    coordinateSlice (schwartzCoordinateDeriv i Φ) i y =
      SchwartzMap.derivCLM ℂ ℂ (coordinateSlice Φ i y) := by
  ext t
  rw [coordinateSlice_apply, SchwartzMap.derivCLM_apply]
  have hL := ((singleCoordinate i).toContinuousLinearMap.hasFDerivAt (x := t)).add_const
    (insertCoordinate i (y, 0))
  have hΦ := (Φ.hasFDerivAt (singleCoordinate i t + insertCoordinate i (y, 0))).comp t hL
  have h := hΦ.hasDerivAt
  have h' : HasDerivAt (coordinateSlice Φ i y)
      (fderiv ℝ Φ (insertCoordinate i (y, t)) (Pi.single i 1 : R)) t := by
    change HasDerivAt (fun z => Φ (singleCoordinate i z + insertCoordinate i (y, 0))) _ t
    have hdir : singleCoordinate i 1 = (Pi.single i 1 : R) := rfl
    rw [insertCoordinate_eq i y t, ← hdir]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      Function.comp_def] at h
    exact h
  exact h'.deriv.symm

private theorem coordinateMellin_split (Φ : SchwartzMap R ℂ) (i : ι)
    {s : ι → ℂ} (hs : ∀ j, 0 < (s j).re) :
    coordinateMellin Φ s =
      ∫ y : ComplementCoordinates i, (∏ j : {j // j ≠ i}, (y j : ℂ) ^ (s j - 1)) *
        mellin (coordinateSlice Φ i y) (s i) ∂positiveCoordinateMeasure {j // j ≠ i} := by
  let μ := positiveCoordinateMeasure {j : ι // j ≠ i}
  let E := insertCoordinate i
  have hI : Integrable (fun p => coordinateMellinIntegrand Φ s (E p)) (μ.prod positiveLineMeasure) :=
    (measurePreserving_insertCoordinate i).integrable_comp_of_integrable
      (integrable_coordinateMellinIntegrand Φ hs)
  rw [coordinateMellin, ← (measurePreserving_insertCoordinate i).integral_comp', integral_prod _ hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (∫ t, coordinateMellinIntegrand Φ s (E (y, t)) ∂positiveLineMeasure) =
      (∏ j : {j // j ≠ i}, (y j : ℂ) ^ (s j - 1)) * mellin (coordinateSlice Φ i y) (s i)
    rw [mellin, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      change (Φ (insertCoordinate i (y, t)) *
        ∏ j, (insertCoordinate i (y, t) j : ℂ) ^ (s j - 1)) =
        (∏ j : {j // j ≠ i}, (y j : ℂ) ^ (s j - 1)) *
          ((t : ℂ) ^ (s i - 1) • coordinateSlice Φ i y t)
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, insertCoordinate_same, coordinateSlice_apply]
      simp_rw [insertCoordinate_other]
      simp only [smul_eq_mul]
      ring

/-- Coordinate integration by parts shifts only the corresponding
positive-orthant Mellin exponent. -/
theorem coordinateMellin_schwartzCoordinateDeriv (Φ : SchwartzMap R ℂ) (i : ι)
    {s : ι → ℂ} (hs : ∀ j, 0 < (s j).re) :
    coordinateMellin (schwartzCoordinateDeriv i Φ) (s + Pi.single i 1) =
      -(s i) * coordinateMellin Φ s := by
  let s' : ι → ℂ := s + Pi.single i 1
  have hs' (j : ι) : 0 < (s' j).re := by
    rcases eq_or_ne j i with he | hj
    · subst j
      simpa only [s', Pi.add_apply, Pi.single_eq_same, Complex.add_re, Complex.one_re] using
        add_pos (hs i) zero_lt_one
    · simpa only [s', Pi.add_apply, Pi.single_eq_of_ne hj, add_zero] using hs j
  change coordinateMellin (schwartzCoordinateDeriv i Φ) s' = _
  rw [coordinateMellin_split _ i hs', coordinateMellin_split _ i hs, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (∏ j : {j // j ≠ i}, (y j : ℂ) ^ (s' j - 1)) *
      mellin (coordinateSlice (schwartzCoordinateDeriv i Φ) i y) (s' i) =
      -(s i) * ((∏ j : {j // j ≠ i}, (y j : ℂ) ^ (s j - 1)) *
        mellin (coordinateSlice Φ i y) (s i))
    have h₀ (j : {j : ι // j ≠ i}) : s' j = s j := by
      simp only [s', Pi.add_apply, Pi.single_eq_of_ne j.property, add_zero]
    have h₁ : s' i = s i + 1 := by simp only [s', Pi.add_apply, Pi.single_eq_same]
    simp only [coordinateSlice_deriv, h₀, h₁, mellin_schwartz_deriv_succ _ (hs i)]
    ring

end Langlands.Analysis
