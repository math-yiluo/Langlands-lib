import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryStatement
import Langlands.LinearAlgebra.GramQuadraticComparison

/-! # The quadratic-form Hasse principle implies the Gram-matrix version -/

noncomputable section

universe u w

open Matrix

namespace Langlands.LinearAlgebra.OrthogonalCocycleDescent

variable {F : Type u} [Field F] [CharZero F]
  {n : Type w} [Fintype n] [DecidableEq n]

/-- A symmetric invertible Gram matrix over a characteristic-zero field has nondegenerate
quadratic polar form. -/
theorem polar_nondegenerate_of_symmetric_unit {B : Matrix n n F}
    (hB : Bᵀ = B) (hu : IsUnit B) : B.toQuadraticForm'.polarBilin.Nondegenerate := by
  let b : LinearMap.BilinForm F (n → F) := Matrix.toLinearMap₂' F B
  have hb : b.Nondegenerate :=
    (LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero).mpr
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det B).mp hu))
  have hp (x y : n → F) : B.toQuadraticForm'.polarBilin x y = (2 : F) * b x y := by
    change QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap b) x y = _
    rw [LinearMap.BilinMap.polar_toQuadraticMap,
      ← bilinear_symm_of_matrix_symm hB x y]
    exact (two_mul (b x y)).symm
  constructor
  · intro x hx
    apply hb.1 x
    intro y
    exact (mul_eq_zero.mp ((hp x y).symm.trans (hx y))).resolve_left two_ne_zero
  · intro y hy
    apply hb.2 y
    intro x
    exact (mul_eq_zero.mp ((hp x y).symm.trans (hy x))).resolve_left two_ne_zero

end Langlands.LinearAlgebra.OrthogonalCocycleDescent

namespace Langlands

open LinearAlgebra.OrthogonalCocycleDescent

/-- Local-to-global congruence for symmetric invertible Gram matrices over every number field.
This is an internal matrix version of the classical quadratic isometry statement. -/
def NumberFieldGramIsometryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (B₁ B₂ : Matrix (Fin n) (Fin n) F),
    B₁ᵀ = B₁ → B₂ᵀ = B₂ → IsUnit B₁ → IsUnit B₂ →
    (∀ v : Global.Place F,
      GramCongruent (B₁.map (algebraMap F (Global.placeCompletion F v)))
        (B₂.map (algebraMap F (Global.placeCompletion F v)))) →
    GramCongruent B₁ B₂

/-- Native quadratic-form isometry over number fields gives local-to-global Gram congruence. -/
theorem numberFieldGramIsometry_of_quadratic
    (h : NumberFieldQuadraticIsometryStatement.{u}) : NumberFieldGramIsometryStatement.{u} := by
  intro F _ _ n B₁ B₂ hs₁ hs₂ hu₁ hu₂ hlocal
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  apply gramCongruent_of_equivalent hs₁ hs₂
  apply h F n B₁.toQuadraticForm' B₂.toQuadraticForm'
    (polar_nondegenerate_of_symmetric_unit hs₁ hu₁)
    (polar_nondegenerate_of_symmetric_unit hs₂ hu₂)
  intro v
  let A := Global.placeCompletion F v
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
  have hmap₁ : (B₁.map (algebraMap F A))ᵀ = B₁.map (algebraMap F A) := by
    rw [← Matrix.transpose_map, hs₁]
  have hmap₂ : (B₂.map (algebraMap F A))ᵀ = B₂.map (algebraMap F A) := by
    rw [← Matrix.transpose_map, hs₂]
  obtain ⟨e⟩ := (gramCongruent_iff_equivalent hmap₁ hmap₂).mp (hlocal v)
  exact ⟨((gramBaseChangeIsometry (A := A) B₁).trans e).trans
    (gramBaseChangeIsometry (A := A) B₂).symm⟩

end Langlands
