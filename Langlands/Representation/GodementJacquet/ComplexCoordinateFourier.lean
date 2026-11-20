import Langlands.Analysis.SchwartzMarginal
import Langlands.Analysis.SchwartzWeightedMarginal
import Langlands.Representation.GodementJacquet.ComplexScalarFourierInversion

/-! # Fourier integration on finite products of the complex trace space -/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

universe u v
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

/-- The product of the scalar self-dual additive measures. -/
def complexCoordinateMeasure (ι : Type*) [Fintype ι] (a : ℂˣ) : Measure (ι → ℂ) :=
  Measure.pi (fun _ => (complexSelfDualMeasure a).measure)

local instance coordinateScalarHaar (a : ℂˣ) : (complexSelfDualMeasure a).measure.IsAddHaarMeasure :=
  (complexSelfDualMeasure a).isAddHaar

instance complexCoordinateMeasure_isAddHaar (a : ℂˣ) :
    (complexCoordinateMeasure ι a).IsAddHaarMeasure := by
  unfold complexCoordinateMeasure
  infer_instance

/-- The complex bilinear coordinate pairing. -/
def complexCoordinatePair (x y : ι → ℂ) : ℂ := ∑ i, x i * y i

theorem continuous_complexCoordinatePair (x : ι → ℂ) :
    Continuous (fun y => complexCoordinatePair y x) :=
  continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)

@[simp]
theorem complexCoordinatePair_zero_right (x : ι → ℂ) :
    complexCoordinatePair x 0 = 0 := by simp [complexCoordinatePair]

/-- The transform with the positive trace pairing on all coordinates. -/
def complexCoordinateFourier (a : ℂˣ) (f : (ι → ℂ) → ℂ) (x : ι → ℂ) : ℂ :=
  ∫ y, f y * traceCharacter a (complexCoordinatePair y x) ∂complexCoordinateMeasure ι a

/-- A permutation of coordinates preserves the self-dual product measure. -/
theorem measurePreserving_complexCoordinateReindex (a : ℂˣ) (e : ι ≃ κ) :
    MeasurePreserving (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => ℂ) e)
      (complexCoordinateMeasure ι a) (complexCoordinateMeasure κ a) :=
  measurePreserving_piCongrLeft (fun _ : κ => (complexSelfDualMeasure a).measure) e

theorem complexCoordinatePair_reindex (e : ι ≃ κ) (x y : ι → ℂ) :
    complexCoordinatePair (fun j => x (e.symm j)) (fun j => y (e.symm j)) =
      complexCoordinatePair x y := by
  exact e.symm.sum_comp (fun i => x i * y i)

omit [Fintype ι] [Fintype κ] in
theorem complexCoordinateReindex_apply (e : ι ≃ κ) (y : ι → ℂ) :
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => ℂ) e y = fun j => y (e.symm j) := by
  funext j
  change Equiv.piCongrLeft (fun _ : κ => ℂ) e y j = _
  rw [Equiv.piCongrLeft_apply_eq_cast]
  rfl

/-- Fourier integration commutes with any simultaneous reindexing of
the function and the frequency coordinates. -/
theorem complexCoordinateFourier_reindex (a : ℂˣ) (e : ι ≃ κ)
    (f : (κ → ℂ) → ℂ) (x : ι → ℂ) :
    complexCoordinateFourier a (fun z => f (fun j => z (e.symm j))) x =
      complexCoordinateFourier a f (fun j => x (e.symm j)) := by
  let E := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => ℂ) e
  let g (y : κ → ℂ) := f y * traceCharacter a (complexCoordinatePair y (E x))
  have hE (y : ι → ℂ) : E y = fun j => y (e.symm j) := complexCoordinateReindex_apply e y
  calc
    _ = ∫ y, g (E y) ∂complexCoordinateMeasure ι a := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [g, hE, complexCoordinatePair_reindex e]
    _ = ∫ y, g y ∂complexCoordinateMeasure κ a :=
      (measurePreserving_complexCoordinateReindex a e).integral_comp
      E.toHomeomorph.measurableEmbedding g
    _ = _ := by simp only [g, hE, complexCoordinateFourier]

/-- The coordinate transform realizes a Schwartz function for each finite
index type. -/
theorem exists_schwartz_complexCoordinateFourier (a : ℂˣ) (Φ : SchwartzMap (ι → ℂ) ℂ) :
    ∃ Ψ : SchwartzMap (ι → ℂ) ℂ, (Ψ : (ι → ℂ) → ℂ) = complexCoordinateFourier a Φ := by
  let e := Fintype.equivFin ι
  let E := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (Fintype.card ι) => ℂ) e
  let H := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm Φ
  obtain ⟨H', hH'⟩ := Langlands.Global.RankinSelbergGlobal.exists_schwartz_complexFourierTransform a H
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E H', funext fun x => ?_⟩
  have h (y : ι → ℂ) : H (fun j => y (e.symm j)) = Φ y := by
    rw [← complexCoordinateReindex_apply e y]
    change Φ (E.symm (E y)) = Φ y
    rw [E.symm_apply_apply]
  change H' (E x) = _
  rw [congrFun hH' (E x)]
  rw [show E x = _ from complexCoordinateReindex_apply e x]
  change complexCoordinateFourier a H (fun j => x (e.symm j)) = _
  rw [← complexCoordinateFourier_reindex a e H x]
  simp only [h]

theorem integrable_complexCoordinateFourier (a : ℂˣ) (Φ : SchwartzMap (ι → ℂ) ℂ) :
    Integrable (complexCoordinateFourier a Φ) (complexCoordinateMeasure ι a) := by
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexCoordinateFourier a Φ
  rw [← hΨ]
  exact Ψ.integrable

private abbrev optionCoordinates (ι : Type*) :
    (Option ι → ℂ) ≃ᵐ (ι → ℂ) × ℂ :=
  MeasurableEquiv.piOptionEquivProd (fun _ => ℂ)

private def optionCoordinatesCLE (ι : Type*) [Fintype ι] :
    (Option ι → ℂ) ≃L[ℝ] (ι → ℂ) × ℂ :=
  ((LinearEquiv.piOptionEquivProd (M := fun _ : Option ι => ℂ) ℝ).trans
    (LinearEquiv.prodComm ℝ ℂ (ι → ℂ))).toContinuousLinearEquiv

private theorem measurePreserving_optionCoordinates (a : ℂˣ) :
    MeasurePreserving (optionCoordinates ι).symm
      ((complexCoordinateMeasure ι a).prod (complexSelfDualMeasure a).measure)
      (complexCoordinateMeasure (Option ι) a) :=
  ⟨(optionCoordinates ι).symm.measurable,
    Measure.pi_map_piOptionEquivProd (fun _ : Option ι => (complexSelfDualMeasure a).measure)⟩

private theorem complexCoordinatePair_option (p q : (ι → ℂ) × ℂ) :
    complexCoordinatePair ((optionCoordinates ι).symm p) ((optionCoordinates ι).symm q) =
      p.2 * q.2 + complexCoordinatePair p.1 q.1 := by
  rw [complexCoordinatePair, Fintype.sum_option]
  rfl

private theorem complexCoordinateFourier_option (a : ℂˣ)
    (Φ : SchwartzMap (Option ι → ℂ) ℂ) (x : ι → ℂ) (z : ℂ) :
    complexCoordinateFourier a Φ ((optionCoordinates ι).symm (x, z)) =
      complexScalarFourier a
        (fun w => ∫ y, Φ ((optionCoordinates ι).symm (y, w)) *
          traceCharacter a (complexCoordinatePair y x) ∂complexCoordinateMeasure ι a) z := by
  let ν := (complexSelfDualMeasure a).measure
  let μ := complexCoordinateMeasure ι a
  let e := optionCoordinates ι
  let f (v : Option ι → ℂ) := Φ v * traceCharacter a (complexCoordinatePair v (e.symm (x, z)))
  have hf : Integrable f (complexCoordinateMeasure (Option ι) a) :=
    (Φ.integrable (μ := complexCoordinateMeasure (Option ι) a)).norm.mono'
      (Φ.continuous.mul ((continuous_traceCharacter a).comp
      (continuous_complexCoordinatePair _))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by simp [f])
  have hfe : Integrable (fun p => f (e.symm p)) (μ.prod ν) :=
    (measurePreserving_optionCoordinates a).integrable_comp_of_integrable hf
  change (∫ v, f v ∂complexCoordinateMeasure (Option ι) a) = _
  rw [← (measurePreserving_optionCoordinates a).integral_comp' f, integral_prod_symm _ hfe]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change (∫ y, f (e.symm (y, w)) ∂μ) =
      (∫ y, Φ (e.symm (y, w)) * traceCharacter a (complexCoordinatePair y x) ∂μ) *
        traceCharacter a (w * z)
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change Φ (e.symm (y, w)) * traceCharacter a
          (complexCoordinatePair (e.symm (y, w)) (e.symm (x, z))) = _
      rw [complexCoordinatePair_option, add_comm (w * z), traceCharacter_add]
      exact (mul_assoc _ _ _).symm

private theorem integral_complexCoordinateFourier_zero_option (a : ℂˣ)
    (hrec : ∀ Φ : SchwartzMap (ι → ℂ) ℂ,
      (∫ x, complexCoordinateFourier a Φ x ∂complexCoordinateMeasure ι a) = Φ 0)
    (Φ : SchwartzMap (Option ι → ℂ) ℂ) :
    (∫ x, complexCoordinateFourier a Φ x ∂complexCoordinateMeasure (Option ι) a) = Φ 0 := by
  let ν := (complexSelfDualMeasure a).measure
  let μ := complexCoordinateMeasure ι a
  let e := optionCoordinates ι
  let E := optionCoordinatesCLE ι
  let Φp := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm Φ
  let Ψ := Langlands.Analysis.schwartzSlice Φp (0 : ℂ)
  have hΦp (p : (ι → ℂ) × ℂ) : Φp p = Φ (e.symm p) := by
    change Φ (E.symm p) = _
    congr 1
    funext i
    cases i <;> rfl
  have hI : Integrable (fun p => complexCoordinateFourier a Φ (e.symm p)) (μ.prod ν) :=
    (measurePreserving_optionCoordinates a).integrable_comp_of_integrable
      (integrable_complexCoordinateFourier a Φ)
  rw [← (measurePreserving_optionCoordinates a).integral_comp' (complexCoordinateFourier a Φ),
    integral_prod _ hI]
  calc
    _ = ∫ x, complexCoordinateFourier a Ψ x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        let K (y : ι → ℂ) := traceCharacter a (complexCoordinatePair y x)
        let Φs := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.prodComm ℝ ℂ (ι → ℂ)) Φp
        let S := Langlands.Analysis.schwartzBoundedMarginal μ K
          ((continuous_traceCharacter a).comp (continuous_complexCoordinatePair x)).measurable
          (fun y => le_of_eq (norm_traceCharacter a (complexCoordinatePair y x))) Φs
        have hS (w : ℂ) : S w = ∫ y, Φ (e.symm (y, w)) * K y ∂μ := by
          rw [Langlands.Analysis.schwartzBoundedMarginal_apply]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            change K y * Φp (y, w) = _
            rw [hΦp, mul_comm]
        have hFz (z : ℂ) : complexCoordinateFourier a Φ (e.symm (x, z)) =
            complexScalarFourier a S z := by
          rw [complexCoordinateFourier_option]
          exact congrArg (fun H => complexScalarFourier a H z) (funext hS).symm
        change (∫ z, complexCoordinateFourier a Φ (e.symm (x, z)) ∂ν) = _
        simp only [hFz]
        rw [show (∫ z, complexScalarFourier a S z ∂ν) = S 0 from
          integral_complexScalarFourier_zero a S]
        have hΨ (y : ι → ℂ) : Ψ y = Φ (e.symm (y, 0)) :=
          (Langlands.Analysis.schwartzSlice_apply Φp 0 y).trans (hΦp _)
        rw [hS, complexCoordinateFourier]
        simp only [hΨ, K, μ]
    _ = Ψ 0 := hrec Ψ
    _ = Φ 0 := by
      rw [Langlands.Analysis.schwartzSlice_apply, hΦp]
      congr 1
      funext i
      cases i <;> rfl

/-- Product Fourier inversion at zero, with the same measure in each
coordinate on the two sides. -/
theorem integral_complexCoordinateFourier_zero (a : ℂˣ) (Φ : SchwartzMap (ι → ℂ) ℂ) :
    (∫ x, complexCoordinateFourier a Φ x ∂complexCoordinateMeasure ι a) = Φ 0 := by
  refine Fintype.induction_empty_option (P := fun J _ => ∀ H : SchwartzMap (J → ℂ) ℂ,
    (∫ x, complexCoordinateFourier a H x ∂complexCoordinateMeasure J a) = H 0)
    ?_ ?_ ?_ ι Φ
  · intro J L _ e ih H
    let : Fintype J := Fintype.ofEquiv L e.symm
    let E := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : L => ℂ) e
    let H' : SchwartzMap (J → ℂ) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E H
    have hF (x : J → ℂ) : complexCoordinateFourier a H' x = complexCoordinateFourier a H (E x) := by
      change complexCoordinateFourier a (H ∘ E) x = _
      have hE (y : J → ℂ) : E y = fun j => y (e.symm j) := complexCoordinateReindex_apply e y
      simpa only [Function.comp_def, hE] using complexCoordinateFourier_reindex a e H x
    calc
      _ = ∫ x : J → ℂ, complexCoordinateFourier a H (E x) ∂complexCoordinateMeasure J a :=
        ((measurePreserving_complexCoordinateReindex a e).integral_comp
          E.toHomeomorph.measurableEmbedding (complexCoordinateFourier a H)).symm
      _ = ∫ x : J → ℂ, complexCoordinateFourier a H' x ∂complexCoordinateMeasure J a :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hF x).symm)
      _ = H' 0 := ih H'
      _ = H 0 := by
        change H (E 0) = _
        rw [map_zero]
  · intro H
    rw [complexCoordinateMeasure, Measure.pi_of_empty _ (0 : PEmpty.{u+1} → ℂ), integral_dirac]
    simp [complexCoordinateFourier, complexCoordinateMeasure,
      Measure.pi_of_empty _ (0 : PEmpty.{u+1} → ℂ)]
  · intro J _ ih H
    exact integral_complexCoordinateFourier_zero_option a ih H

end Langlands.GodementJacquet
