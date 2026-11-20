import Langlands.Global.RankinSelberg.RectangleTateMeasure
import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.Representation.GodementJacquet.ComplexFourierMarginal
import Langlands.Representation.GodementJacquet.ComplexTriangularMatrixEntries

/-! # The strict triangular marginals of the complex matrix Fourier transform -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.LocalFactor.Archimedean

variable {n : ℕ}
local notation "I" => Fin n
local notation "J" => UpperEntryPair n
local notation "M" => Matrix I I ℂ
local notation "D" => I → ℂ
local notation "U" => J → ℂ
local notation "S" => (I ⊕ J) ⊕ J

local instance matrixFourierScalarHaar (a : ℂˣ) : (complexSelfDualMeasure a).measure.IsAddHaarMeasure :=
  (complexSelfDualMeasure a).isAddHaar

variable (n)

private def matrixEntryIndex : S ≃ I × I where
  toFun
    | .inl (.inl i) => (i, i)
    | .inl (.inr p) => p.1
    | .inr p => p.1.swap
  invFun p :=
    if h : p.1 = p.2 then .inl (.inl p.1)
    else if h' : p.1 < p.2 then .inl (.inr ⟨p, h'⟩)
    else .inr ⟨p.swap, lt_of_le_of_ne (le_of_not_gt h') (Ne.symm h)⟩
  left_inv := by
    rintro ((i | ⟨⟨i, j⟩, h⟩) | ⟨⟨i, j⟩, h⟩)
    · simp
    · simp [ne_of_lt h, h]
    · simp [ne_of_gt h, not_lt_of_gt h]
  right_inv := by
    rintro ⟨i, j⟩
    rcases lt_trichotomy i j with h | rfl | h
    · simp [ne_of_lt h, h]
    · simp
    · simp [ne_of_gt h, not_lt_of_gt h]

private def matrixUncurry : M ≃L[ℝ] (I × I → ℂ) where
  toFun X p := X p.1 p.2
  invFun X := Matrix.of fun i j => X (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2
  continuous_invFun := continuous_matrix fun i j => continuous_apply (i, j)

private def matrixSplitSum : (S → ℂ) ≃L[ℝ] ((D × U) × U) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (I ⊕ J) J (fun _ => ℂ)).trans
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ I J (fun _ => ℂ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ U))

/-- Separate the diagonal, strict upper and strict lower entries. The lower
entries are indexed by the transposes of the strict upper entries. -/
def complexMatrixCoordinates : M ≃L[ℝ] ((D × U) × U) :=
  ((matrixUncurry n).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : S => ℂ) (matrixEntryIndex n).symm)).trans
      (matrixSplitSum n)

variable {n}

theorem complexMatrixCoordinates_apply (X : M) :
    complexMatrixCoordinates n X =
      ((fun i => X i i, fun j => X j.1.1 j.1.2), fun j => X j.1.2 j.1.1) := by
  let e := (matrixEntryIndex n).symm
  change matrixSplitSum n ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : S => ℂ) e)
    (matrixUncurry n X)) = _
  rw [complexCoordinateReindex_apply e]
  rfl

private theorem matrixSplitSum_measurePreserving (a : ℂˣ) :
    MeasurePreserving (matrixSplitSum n) (complexCoordinateMeasure S a)
      (((complexCoordinateMeasure I a).prod (complexCoordinateMeasure J a)).prod
        (complexCoordinateMeasure J a)) := by
  have h := measurePreserving_sumPiEquivProdPi
    (fun _ : S => (complexSelfDualMeasure a).measure)
  have h' := measurePreserving_sumPiEquivProdPi
    (fun _ : I ⊕ J => (complexSelfDualMeasure a).measure)
  exact (h'.prod (MeasurePreserving.id (complexCoordinateMeasure J a))).comp h

variable (n) in
theorem measurePreserving_complexMatrixCoordinates (a : ℂˣ) :
    MeasurePreserving (complexMatrixCoordinates n)
      (RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) n n)
      (((complexCoordinateMeasure I a).prod (complexCoordinateMeasure J a)).prod
        (complexCoordinateMeasure J a)) := by
  have hu : MeasurePreserving (matrixUncurry n)
      (RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) n n)
      (complexCoordinateMeasure (I × I) a) :=
    Langlands.Global.RankinSelbergGlobal.RectangleTate.measurePreserving_uncurry
      (fun _ : I => fun _ : I => (complexSelfDualMeasure a).measure)
  exact (matrixSplitSum_measurePreserving a).comp
    ((measurePreserving_complexCoordinateReindex a (matrixEntryIndex n).symm).comp hu)

/-- Schwartz closure for the actual rectangular Fourier integral on square
complex matrices. -/
theorem exists_schwartz_complexMatrixFourier (a : ℂˣ) (Φ : SchwartzMap M ℂ) :
    ∃ Ψ : SchwartzMap M ℂ, (Ψ : M → ℂ) =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) Φ := by
  let E := matrixUncurry n
  let H := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm Φ
  obtain ⟨H', hH⟩ := exists_schwartz_complexCoordinateFourier a H
  have hμ : MeasurePreserving E (RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) n n)
      (complexCoordinateMeasure (I × I) a) :=
    Langlands.Global.RankinSelbergGlobal.RectangleTate.measurePreserving_uncurry
      (fun _ : I => fun _ : I => (complexSelfDualMeasure a).measure)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E H', funext fun X => ?_⟩
  change H' (E X) = _
  rw [congrFun hH (E X)]
  let f (Y : I × I → ℂ) := H Y * traceCharacter a (complexCoordinatePair Y (E X))
  change (∫ Y, f Y ∂complexCoordinateMeasure (I × I) a) = _
  rw [← hμ.integral_comp E.toHomeomorph.measurableEmbedding f]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun Y => by
    change Φ (E.symm (E Y)) * traceCharacter a (complexCoordinatePair (E Y) (E X)) =
      Φ Y * traceCharacter a (rectangularPairing Y X)
    rw [E.symm_apply_apply]
    have hp : complexCoordinatePair (E Y) (E X) = rectangularPairing Y X :=
      Fintype.sum_prod_type' (fun (i j : I) => Y i j * X i j)
    rw [hp]

private theorem rectangularPairing_split (X Y : M) :
    rectangularPairing X Y =
      complexCoordinatePair (complexMatrixCoordinates n X).1.1 (complexMatrixCoordinates n Y).1.1 +
        complexCoordinatePair (complexMatrixCoordinates n X).1.2 (complexMatrixCoordinates n Y).1.2 +
        complexCoordinatePair (complexMatrixCoordinates n X).2 (complexMatrixCoordinates n Y).2 := by
  simp only [rectangularPairing, complexMatrixCoordinates_apply, complexCoordinatePair]
  rw [← Fintype.sum_prod_type' (fun (i j : I) => X i j * Y i j)]
  rw [← (matrixEntryIndex n).sum_comp (fun p : I × I => X p.1 p.2 * Y p.1 p.2)]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

theorem complexMatrixCoordinates_symm_upper (d : D) (x : U) :
    (complexMatrixCoordinates n).symm ((d, x), 0) = complexTriangularMatrix d x := by
  apply (complexMatrixCoordinates n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, complexMatrixCoordinates_apply]
  apply Prod.ext
  · apply Prod.ext
    · funext i
      simp [complexTriangularMatrix]
    · funext p
      simp [complexTriangularMatrix, p.property]
  · funext p
    simp [complexTriangularMatrix, not_lt_of_gt p.property, ne_of_gt p.property]

theorem complexMatrixCoordinates_symm_lower (d : D) (x : U) :
    (complexMatrixCoordinates n).symm ((d, 0), x) = (complexTriangularMatrix d x).transpose := by
  apply (complexMatrixCoordinates n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, complexMatrixCoordinates_apply]
  apply Prod.ext
  · apply Prod.ext
    · funext i
      simp [complexTriangularMatrix]
    · funext p
      simp [complexTriangularMatrix, not_lt_of_gt p.property, ne_of_gt p.property]
  · funext p
    simp [complexTriangularMatrix, p.property]

/-- For the self-dual product measures the strict lower marginal of the
matrix transform is the diagonal transform of the strict upper marginal. -/
theorem integral_rectangularFourierIntegral_lower (a : ℂˣ) (Φ : SchwartzMap M ℂ) (d : D) :
    (∫ x : U, rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
      Φ (complexTriangularMatrix d x).transpose ∂complexCoordinateMeasure J a) =
      complexCoordinateFourier a
        (fun c : D => ∫ x : U, Φ (complexTriangularMatrix c x) ∂complexCoordinateMeasure J a) d := by
  let e := complexMatrixCoordinates n
  let Ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Φ
  have hF (y : (D × U) × U) :
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
        Φ (e.symm y) = complexBlockFourier a Ψ y := by
    let f (z : (D × U) × U) := Φ (e.symm z) * traceCharacter a
      (complexCoordinatePair z.1.1 y.1.1 + complexCoordinatePair z.1.2 y.1.2 +
        complexCoordinatePair z.2 y.2)
    change _ = ∫ z, f z ∂_
    rw [← (measurePreserving_complexMatrixCoordinates n a).integral_comp
      e.toHomeomorph.measurableEmbedding f]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X => by
      change Φ X * traceCharacter a (rectangularPairing X (e.symm y)) = f (e X)
      simp only [f, rectangularPairing_split, e.apply_symm_apply, e.symm_apply_apply, e]
  calc
    _ = ∫ x : U, complexBlockFourier a Ψ ((d, 0), x) ∂complexCoordinateMeasure J a := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simpa only [e, complexMatrixCoordinates_symm_lower] using hF ((d, 0), x)
    _ = _ := by
      rw [integral_complexBlockFourier_complement]
      congr 1
      funext c
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change Φ (e.symm ((c, x), 0)) = _
        rw [complexMatrixCoordinates_symm_upper]

end Langlands.GodementJacquet
