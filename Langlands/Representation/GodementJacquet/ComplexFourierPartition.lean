import Langlands.Representation.GodementJacquet.ComplexFourierAffineSlice
import Langlands.Global.RankinSelberg.RectangleTateMeasure
import Langlands.HarmonicAnalysis.RectangularFourier

/-! # Fourier inversion for complementary groups of matrix entries -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

section Partition

variable {ι : Type*} [Fintype ι]
variable (P : ι → Prop) [DecidablePred P]

local notation "A" => {i : ι // P i} → ℂ
local notation "B" => {i : ι // ¬P i} → ℂ

/-- Partition the coordinate functions by a predicate on their finite index set. -/
def complexPartitionCoordinates : (ι → ℂ) ≃L[ℝ] A × B :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : {i : ι // P i} ⊕ {i : ι // ¬P i} => ℂ)
    (Equiv.sumCompl P).symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℝ {i : ι // P i} {i : ι // ¬P i} (fun _ => ℂ))

omit [Fintype ι] in
theorem complexPartitionCoordinates_apply (x : ι → ℂ) :
    complexPartitionCoordinates P x = (fun i => x i.val, fun j => x j.val) := by
  unfold complexPartitionCoordinates
  rw [ContinuousLinearEquiv.trans_apply, complexCoordinateReindex_apply]
  rfl

theorem measurePreserving_complexPartitionCoordinates (a : ℂˣ) :
    MeasurePreserving (complexPartitionCoordinates P) (complexCoordinateMeasure ι a)
      ((complexCoordinateMeasure {i : ι // P i} a).prod
        (complexCoordinateMeasure {i : ι // ¬P i} a)) := by
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  exact (measurePreserving_sumPiEquivProdPi (fun _ => (complexSelfDualMeasure a).measure)).comp
    (measurePreserving_complexCoordinateReindex a (Equiv.sumCompl P).symm)

private theorem complexCoordinatePair_partition (x z : ι → ℂ) :
    complexCoordinatePair x z =
      complexCoordinatePair (complexPartitionCoordinates P x).1 (complexPartitionCoordinates P z).1 +
        complexCoordinatePair (complexPartitionCoordinates P x).2 (complexPartitionCoordinates P z).2 := by
  rw [complexPartitionCoordinates_apply, complexPartitionCoordinates_apply]
  unfold complexCoordinatePair
  rw [← (Equiv.sumCompl P).sum_comp (fun i => x i * z i), Fintype.sum_sum_type]
  rfl

private theorem complexTwoBlockFourier_partition (a : ℂˣ) (Φ : (ι → ℂ) → ℂ) (v : A × B) :
    complexTwoBlockFourier a (Φ ∘ (complexPartitionCoordinates P).symm) v =
      complexCoordinateFourier a Φ ((complexPartitionCoordinates P).symm v) := by
  let E := complexPartitionCoordinates P
  let H (y : A × B) := Φ (E.symm y) * traceCharacter a
    (complexCoordinatePair y.1 v.1 + complexCoordinatePair y.2 v.2)
  change (∫ y, H y ∂(complexCoordinateMeasure {i : ι // P i} a).prod
    (complexCoordinateMeasure {i : ι // ¬P i} a)) = _
  rw [← (measurePreserving_complexPartitionCoordinates P a).integral_comp
    E.toHomeomorph.measurableEmbedding H]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change Φ (E.symm (E x)) * traceCharacter a
      (complexCoordinatePair (E x).1 v.1 + complexCoordinatePair (E x).2 v.2) =
        Φ x * traceCharacter a (complexCoordinatePair x (E.symm v))
    rw [E.symm_apply_apply, complexCoordinatePair_partition P x (E.symm v)]
    rw [show complexPartitionCoordinates P (E.symm v) = v from E.apply_symm_apply v]

/-- Affine Fourier inversion after partitioning the coordinates by a predicate. -/
theorem integral_complexCoordinateFourier_partition (a : ℂˣ) (Φ : SchwartzMap (ι → ℂ) ℂ)
    (z : A) (b : B) :
    Integrable (fun y =>
      complexCoordinateFourier a Φ ((complexPartitionCoordinates P).symm (z, y)) *
        traceCharacter a (-complexCoordinatePair b y))
      (complexCoordinateMeasure {i : ι // ¬P i} a) ∧
    Integrable (fun x => Φ ((complexPartitionCoordinates P).symm (x, b)) *
      traceCharacter a (complexCoordinatePair x z)) (complexCoordinateMeasure {i : ι // P i} a) ∧
    (∫ y, complexCoordinateFourier a Φ ((complexPartitionCoordinates P).symm (z, y)) *
      traceCharacter a (-complexCoordinatePair b y) ∂complexCoordinateMeasure {i : ι // ¬P i} a) =
      ∫ x, Φ ((complexPartitionCoordinates P).symm (x, b)) *
        traceCharacter a (complexCoordinatePair x z) ∂complexCoordinateMeasure {i : ι // P i} a := by
  let Ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexPartitionCoordinates P).symm Φ
  have h := integral_complexTwoBlockFourier_affineSlice a Ψ z b
  simpa only [Ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    complexTwoBlockFourier_partition P a Φ, Function.comp_apply] using h

omit [Fintype ι] in
theorem complexPartitionCoordinates_symm_apply_left (x : A) (y : B) (ij : ι) (h : P ij) :
    (complexPartitionCoordinates P).symm (x, y) ij = x ⟨ij, h⟩ := by
  have he := congrArg Prod.fst
    ((complexPartitionCoordinates P).apply_symm_apply (x, y))
  rw [complexPartitionCoordinates_apply] at he
  exact congrFun he ⟨ij, h⟩

omit [Fintype ι] in
theorem complexPartitionCoordinates_symm_apply_right (x : A) (y : B) (ij : ι) (h : ¬P ij) :
    (complexPartitionCoordinates P).symm (x, y) ij = y ⟨ij, h⟩ := by
  have he := congrArg Prod.snd
    ((complexPartitionCoordinates P).apply_symm_apply (x, y))
  rw [complexPartitionCoordinates_apply] at he
  exact congrFun he ⟨ij, h⟩

end Partition

section Rectangle

variable {m n : ℕ}
local notation "R" => Matrix (Fin m) (Fin n) ℂ
local notation "I" => Fin m × Fin n

/-- Uncurry the row and column indices of a complex matrix. -/
def complexRectangleUncurry (m n : ℕ) : Matrix (Fin m) (Fin n) ℂ ≃L[ℝ] (Fin m × Fin n → ℂ) where
  toFun X p := X p.1 p.2
  invFun X := Matrix.of fun i j => X (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun p => continuous_id.matrix_elem p.1 p.2
  continuous_invFun := continuous_matrix fun i j => continuous_apply (i, j)

theorem measurePreserving_complexRectangleUncurry (a : ℂˣ) :
    MeasurePreserving (complexRectangleUncurry m n)
      (RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) m n)
      (complexCoordinateMeasure I a) := by
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  exact Langlands.Global.RankinSelbergGlobal.RectangleTate.measurePreserving_uncurry
    (fun _ : Fin m => fun _ : Fin n => (complexSelfDualMeasure a).measure)

theorem complexCoordinateFourier_rectangleUncurry (a : ℂˣ) (Φ : R → ℂ) (z : I → ℂ) :
    complexCoordinateFourier a (Φ ∘ (complexRectangleUncurry m n).symm) z =
      rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a) Φ
        ((complexRectangleUncurry m n).symm z) := by
  let E := complexRectangleUncurry m n
  let F (x : I → ℂ) := Φ (E.symm x) * traceCharacter a (complexCoordinatePair x z)
  change (∫ x, F x ∂complexCoordinateMeasure I a) = _
  rw [← (measurePreserving_complexRectangleUncurry a).integral_comp
    E.toHomeomorph.measurableEmbedding F]
  apply integral_congr_ae
  exact Eventually.of_forall fun X => by
    change Φ (E.symm (E X)) * traceCharacter a (complexCoordinatePair (E X) z) =
      Φ X * traceCharacter a (rectangularPairing X (E.symm z))
    have he : complexCoordinatePair (E X) z = rectangularPairing X (E.symm z) :=
      Fintype.sum_prod_type' (fun (i : Fin m) (j : Fin n) => X i j * z (i, j))
    rw [E.symm_apply_apply, he]

end Rectangle

end Langlands.GodementJacquet
