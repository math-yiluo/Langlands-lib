import Langlands.Algebra.BrauerCorestriction.PiMatrixKronecker
import Langlands.Algebra.MatrixGaloisSplitting
import Langlands.Algebra.TensorProductSplittingCharts
import Mathlib.Algebra.Group.Pi.Units

/-! # Matrix descent from the weighted regular representation -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u

namespace Langlands.BrauerComparison

open CentralSimple CentralSimple.SemilinearGaloisAction
open ScalarTwoCocycle (IsTwoCocycle)
open GroupScheme.SpecialLinearInnerForm (conjugationAlgHom)

attribute [local instance] coefficientGLAction Classical.decEq

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The regular matrix sends the basis vector at `t` to `c s t` times the one at `s * t`. -/
def regularLift (c : Gal(L/K) → Gal(L/K) → Lˣ) (s : Gal(L/K)) : GL (Gal(L/K)) L :=
  BrauerCorestriction.permUnit (Equiv.mulLeft s).symm *
    Units.map (Matrix.diagonalRingHom (Gal(L/K)) L).toMonoidHom
      (MulEquiv.piUnits.symm (c s))

@[simp] theorem regularLift_apply (c : Gal(L/K) → Gal(L/K) → Lˣ) (s i j : Gal(L/K)) :
    (regularLift c s : Matrix (Gal(L/K)) (Gal(L/K)) L) i j =
      if i = s * j then (c s j : L) else 0 := by
  change (((Equiv.mulLeft s).symm.toPEquiv.toMatrix : Matrix (Gal(L/K)) (Gal(L/K)) L) *
    diagonal (fun t => (c s t : L))) i j = _
  rw [Matrix.mul_diagonal, PEquiv.toMatrix_apply]
  change (if j ∈ some ((Equiv.mulLeft s).symm i) then (1 : L) else 0) * ↑(c s j) = _
  have h : j ∈ some ((Equiv.mulLeft s).symm i) ↔ i = s * j := by
    constructor
    · intro hj
      have he : (Equiv.mulLeft s).symm i = j := Option.some.inj hj
      exact (Equiv.symm_apply_eq (Equiv.mulLeft s)).mp he
    · intro hij
      exact congrArg some ((Equiv.symm_apply_eq (Equiv.mulLeft s)).mpr hij)
  simp only [h, ite_mul, one_mul, zero_mul]

/-- The weighted regular lifts have the original cocycle as their scalar factor set. -/
theorem regularLift_mul (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c)
    (s t : Gal(L/K)) :
    regularLift c s * (s • regularLift c t) =
      GeneralLinearGroup.scalar (Gal(L/K)) (c s t) * regularLift c (s * t) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, coefficientGLAction_coe, GeneralLinearGroup.coe_scalar]
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [regularLift_apply, Matrix.map_apply, apply_ite s, map_zero]
  rw [Finset.sum_eq_single (t * j)]
  · have h := congrArg Units.val (hc s t j)
    change (c s t : L) * (c (s * t) j : L) = s (c t j : L) * (c s (t * j) : L) at h
    rw [mul_assoc s t j]
    by_cases hi : i = s * (t * j)
    · simp only [hi, ite_true, ← h, mul_comm (c s (t * j) : L)]
    · simp [hi]
  · intro k _ hk
    simp [hk]
  · simp

/-- Conjugating coefficient automorphisms by the regular matrices gives a semilinear action. -/
def regularAction (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) :
    SemilinearGaloisAction K L (Matrix (Gal(L/K)) (Gal(L/K)) L) where
  act s := (conjugationAlgHom (R := L) (regularLift c s)).toRingHom.comp
    s.mapMatrix.toRingHom
  act_algebraMap s l := by
    have h : (algebraMap L (Matrix (Gal(L/K)) (Gal(L/K)) L) l).map s =
        algebraMap L _ (s l) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    change conjugationAlgHom (R := L) (regularLift c s)
      ((algebraMap L (Matrix (Gal(L/K)) (Gal(L/K)) L) l).map s) = _
    rw [h, AlgHom.commutes]
  act_one X := by
    have h : regularLift c 1 = GeneralLinearGroup.scalar (Gal(L/K)) (c 1 1) := by
      apply mul_right_cancel (b := regularLift c 1)
      simpa only [one_smul, mul_one] using regularLift_mul c hc 1 1
    change (regularLift c 1 : Matrix (Gal(L/K)) (Gal(L/K)) L) *
      X.map (1 : Gal(L/K)) * ((regularLift c 1)⁻¹ : GL (Gal(L/K)) L) = _
    have hX : X.map (1 : Gal(L/K)) = X := rfl
    rw [hX, h]
    simpa only [mul_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] using
      scalar_mul_matrix_conjugation (c 1 1) (1 : GL (Gal(L/K)) L) X
  act_mul s t X := by
    let P := regularLift c
    change (P (s * t) : Matrix (Gal(L/K)) (Gal(L/K)) L) * X.map (s * t) *
      ((P (s * t))⁻¹ : GL (Gal(L/K)) L) =
      (P s : Matrix (Gal(L/K)) (Gal(L/K)) L) *
        (((P t : Matrix (Gal(L/K)) (Gal(L/K)) L) * X.map t *
          ((P t)⁻¹ : GL (Gal(L/K)) L)).map s) * ((P s)⁻¹ : GL (Gal(L/K)) L)
    calc
      _ = ((P s * (s • P t) : GL (Gal(L/K)) L) : Matrix (Gal(L/K)) (Gal(L/K)) L) *
          X.map (s * t) * ((P s * (s • P t))⁻¹ : GL (Gal(L/K)) L) := by
        rw [regularLift_mul c hc]
        exact (scalar_mul_matrix_conjugation (c s t) (P (s * t))
          (X.map (⇑(s * t : Gal(L/K))))).symm
      _ = _ := by
        simp only [Matrix.map_mul, Matrix.map_map, _root_.mul_inv_rev, Units.val_mul,
          ← smul_inv', coefficientGLAction_coe, Matrix.mul_assoc]
        rfl

@[simp] theorem regularAction_apply (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c)
    (s : Gal(L/K)) (X : Matrix (Gal(L/K)) (Gal(L/K)) L) :
    (regularAction c hc).act s X =
      (regularLift c s : Matrix (Gal(L/K)) (Gal(L/K)) L) * X.map s *
        ((regularLift c s)⁻¹ : GL (Gal(L/K)) L) := rfl

variable [IsGalois K L]

/-- The actual central simple algebra obtained by fixing the regular matrix action. -/
def regularCSA (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (regularAction c hc).fixed
  isCentral := (regularAction c hc).isCentral_fixed
  isSimple := (regularAction c hc).isSimpleRing_fixed
  fin_dim := (regularAction c hc).finiteDimensional_fixed

/-- The actual splitting chart for the regular fixed algebra. -/
def regularSplittingChart (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c) :
    L ⊗[K] regularCSA c hc ≃ₐ[L] Matrix (Gal(L/K)) (Gal(L/K)) L :=
  (regularAction c hc).descentEquiv

/-- The descent chart transports the coefficient action back to the regular matrix action. -/
theorem regularSplittingChart_action (c : Gal(L/K) → Gal(L/K) → Lˣ) (hc : IsTwoCocycle c)
    (s : Gal(L/K)) (X : Matrix (Gal(L/K)) (Gal(L/K)) L) :
    (splittingChartIndexAction (regularSplittingChart c hc)).act s X =
      (regularAction c hc).act s X := by
  obtain ⟨Y, rfl⟩ := (regularSplittingChart c hc).surjective X
  rw [splittingChartIndexAction_apply]
  induction Y with
  | tmul l a =>
    rw [tensorCoefficientMap_tmul]
    change ↥(regularAction c hc).fixed at a
    change (regularAction c hc).descentEquiv (s l ⊗ₜ[K] a) =
      (regularAction c hc).act s ((regularAction c hc).descentEquiv (l ⊗ₜ[K] a))
    rw [descentEquiv_tmul, descentEquiv_tmul, map_mul, act_algebraMap, act_fixed]
  | add Y Z hY hZ => simp only [map_add, hY, hZ]

end Langlands.BrauerComparison
