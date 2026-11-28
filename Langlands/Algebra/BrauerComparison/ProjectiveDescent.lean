import Langlands.Algebra.BrauerComparison.Relative
import Langlands.Algebra.MatrixGaloisSplitting
import Langlands.Algebra.TensorProductSplittingCharts
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Matrix

/-! # Matrix descent from projective Galois lifts -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u

namespace Langlands.CentralSimple.SemilinearGaloisAction

open GroupScheme.SpecialLinearInnerForm (conjugationAlgHom)

attribute [local instance] coefficientGLAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {I : Type} [Fintype I] [DecidableEq I]
  (P : Gal(L/K) → GL I L) {c : Gal(L/K) → Gal(L/K) → Lˣ}
  (hc : ∀ s t, P s * (s • P t) = GeneralLinearGroup.scalar I (c s t) * P (s * t))

/-- Coefficient automorphisms followed by conjugation by projective lifts
give a semilinear action on the endomorphism algebra. -/
def ofProjectiveLifts : SemilinearGaloisAction K L (Matrix I I L) where
  act s := (conjugationAlgHom (R := L) (P s)).toRingHom.comp s.mapMatrix.toRingHom
  act_algebraMap s l := by
    have h : (algebraMap L (Matrix I I L) l).map s = algebraMap L _ (s l) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    change conjugationAlgHom (R := L) (P s)
      ((algebraMap L (Matrix I I L) l).map s) = _
    rw [h, AlgHom.commutes]
  act_one X := by
    have h : P 1 = GeneralLinearGroup.scalar I (c 1 1) := by
      apply mul_right_cancel (b := P 1)
      simpa only [one_smul, mul_one] using hc 1 1
    change (P 1 : Matrix I I L) * X.map (1 : Gal(L/K)) * ((P 1)⁻¹ : GL I L) = _
    have hX : X.map (1 : Gal(L/K)) = X := rfl
    rw [hX, h]
    simpa only [mul_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] using
      scalar_mul_matrix_conjugation (c 1 1) (1 : GL I L) X
  act_mul s t X := by
    change (P (s * t) : Matrix I I L) * X.map (s * t) * ((P (s * t))⁻¹ : GL I L) =
      (P s : Matrix I I L) *
        (((P t : Matrix I I L) * X.map t * ((P t)⁻¹ : GL I L)).map s) * ((P s)⁻¹ : GL I L)
    calc
      _ = ((P s * (s • P t) : GL I L) : Matrix I I L) * X.map (s * t) *
          ((P s * (s • P t))⁻¹ : GL I L) := by
        rw [hc]
        exact (scalar_mul_matrix_conjugation (c s t) (P (s * t))
          (X.map (⇑(s * t : Gal(L/K))))).symm
      _ = _ := by
        simp only [Matrix.map_mul, Matrix.map_map, _root_.mul_inv_rev, Units.val_mul,
          ← smul_inv', coefficientGLAction_coe, Matrix.mul_assoc]
        rfl

@[simp] theorem ofProjectiveLifts_act (s : Gal(L/K)) (X : Matrix I I L) :
    (ofProjectiveLifts P hc).act s X =
      (P s : Matrix I I L) * X.map s * ((P s)⁻¹ : GL I L) := rfl

variable [FiniteDimensional K L] [IsGalois K L]

/-- A fixed matrix algebra, viewed as a central simple algebra over the
ground field. -/
def matrixFixedCSA [Nonempty I] (ρ : SemilinearGaloisAction K L (Matrix I I L)) :
    CSA.{u, u} K where
  toAlgCat := AlgCat.of K ρ.fixed
  isCentral := ρ.isCentral_fixed
  isSimple := ρ.isSimpleRing_fixed
  fin_dim := ρ.finiteDimensional_fixed

/-- The splitting chart supplied by Galois descent. -/
def matrixFixedSplittingChart [Nonempty I] (ρ : SemilinearGaloisAction K L (Matrix I I L)) :
    L ⊗[K] matrixFixedCSA ρ ≃ₐ[L] Matrix I I L :=
  ρ.descentEquiv

variable [Nonempty I]

/-- The action transported through the descent chart is the original action. -/
theorem matrixFixedSplittingChart_action (ρ : SemilinearGaloisAction K L (Matrix I I L))
    (s : Gal(L/K)) (X : Matrix I I L) :
    (splittingChartIndexAction (matrixFixedSplittingChart ρ)).act s X = ρ.act s X := by
  obtain ⟨Y, rfl⟩ := (matrixFixedSplittingChart ρ).surjective X
  rw [splittingChartIndexAction_apply]
  induction Y with
  | tmul l a =>
    rw [tensorCoefficientMap_tmul]
    change ↥ρ.fixed at a
    change ρ.descentEquiv (s l ⊗ₜ[K] a) = ρ.act s (ρ.descentEquiv (l ⊗ₜ[K] a))
    rw [descentEquiv_tmul, descentEquiv_tmul, map_mul, act_algebraMap, act_fixed]
  | add Y Z hY hZ => simp only [map_add, hY, hZ]

/-- The factor set of the supplied projective lifts computes the relative
Brauer class in the fixed-algebra chart. -/
theorem relativeClass_ofProjectiveLifts :
    BrauerComparison.relativeClass (matrixFixedSplittingChart (ofProjectiveLifts P hc)) =
      BrauerComparison.unitClass c (ScalarTwoCocycle.isTwoCocycle_of_lifts
        (GeneralLinearGroup.scalar I) unit_scalar_injective unit_scalar_central
        coefficientGLAction_scalar P c hc) := by
  unfold BrauerComparison.relativeClass
  exact BrauerComparison.descentClass_eq_of_lifts _ P c
    (fun s X => (matrixFixedSplittingChart_action (ofProjectiveLifts P hc) s X).trans
      (ofProjectiveLifts_act P hc s X)) hc

end Langlands.CentralSimple.SemilinearGaloisAction
