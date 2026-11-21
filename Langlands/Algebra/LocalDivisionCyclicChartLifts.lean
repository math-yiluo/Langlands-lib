import Langlands.Algebra.LocalDivisionSubfieldOppositeChart
import Langlands.Algebra.LocalDivisionCyclicBasis
import Langlands.Algebra.TensorProductSplittingCharts
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Matrix lifts of the cyclic splitting chart action -/

noncomputable section

namespace Langlands.CentralDivision

open Module Matrix
open scoped TensorProduct MatrixGroups

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable (b : letI := localDivisionSubfieldLeftModule K D ι
              Basis (Fin (CentralSimple.reducedDegree K D)) L D)
variable {σ : L ≃ₐ[K] L} {j : Dˣ}
variable (hj : ∀ a : L, (j : D) * ι a = ι (σ a) * (j : D))

local notation "Index" => Fin (CentralSimple.reducedDegree K D)
local notation "Vec" => (Index → L)

include hj in
private def powerLinearEquiv (n : ℕ) : Vec ≃ₗ[L] Vec := by
  letI := localDivisionSubfieldLeftModule K D ι
  let s := σ ^ n
  let e := b.equivFun
  let a : Vec ≃ Vec := Equiv.piCongrRight fun _ => s.symm.toEquiv
  let p := ((a.trans e.symm.toEquiv).trans (j ^ n).mulLeft).trans e.toEquiv
  have hp (v : Vec) : p v = e ((j : D) ^ n * e.symm (s.symm ∘ v)) := by
    change e (((j ^ n : Dˣ) : D) * _) = _
    rw [Units.val_pow_eq_pow_val]
    rfl
  refine { p with map_add' := ?_, map_smul' := ?_ }
  · intro v w
    have h : s.symm ∘ (v + w) = (s.symm ∘ v) + (s.symm ∘ w) := by
      funext i
      exact s.symm.map_add (v i) (w i)
    change p (v + w) = p v + p w
    simp only [hp, h, map_add, mul_add]
  · intro c v
    have h : s.symm ∘ (c • v) = s.symm c • (s.symm ∘ v) := by
      funext i
      exact s.symm.map_mul c (v i)
    change p (c • v) = c • p v
    simp only [hp, h, e.symm.map_smul]
    rw [← e.map_smul]
    apply congrArg e
    change (j : D) ^ n * (ι (s.symm c) * e.symm (s.symm ∘ v)) =
      ι c * ((j : D) ^ n * e.symm (s.symm ∘ v))
    rw [← mul_assoc, implementingUnit_pow_mul K D ι hj, s.apply_symm_apply, mul_assoc]

/-- Left multiplication by the implementing power, with inverse coefficient
transport, gives an invertible matrix over the actual embedded field. -/
def subfieldCyclicPowerLift (n : ℕ) : GL Index L :=
  Units.map Matrix.toLinAlgEquiv'.symm.toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (powerLinearEquiv K D ι b hj n))

/-- On the coefficient-transformed coordinates the lift is the original left
multiplication by the power in the division algebra. -/
theorem subfieldCyclicPowerLift_mulVec (n : ℕ) (x : D) :
    letI := localDivisionSubfieldLeftModule K D ι
    (subfieldCyclicPowerLift K D ι b hj n : Matrix Index Index L) *ᵥ ((σ ^ n) ∘ b.repr x) =
      b.repr ((j : D) ^ n * x) := by
  let := localDivisionSubfieldLeftModule K D ι
  let s := σ ^ n
  have h := Matrix.toLinAlgEquiv'_apply
    (subfieldCyclicPowerLift K D ι b hj n : Matrix Index Index L) (s ∘ b.repr x)
  rw [← h]
  change Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm
    (powerLinearEquiv K D ι b hj n).toLinearMap) (s ∘ b.repr x) = _
  rw [AlgEquiv.apply_symm_apply]
  change b.equivFun (((j ^ n : Dˣ) : D) * b.equivFun.symm (s.symm ∘ (s ∘ b.repr x))) = _
  have hcoeff : s.symm ∘ (s ∘ b.repr x) = b.equivFun x := by
    funext i
    exact s.symm_apply_apply (b.repr x i)
  rw [hcoeff, b.equivFun.symm_apply_apply, Units.val_pow_eq_pow_val]
  rfl

private theorem map_mulVec_equiv (s : L ≃ₐ[K] L) (A : Matrix Index Index L) (v : Vec) :
    A.map s *ᵥ (s ∘ v) = s ∘ (A *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec s.toRingHom A v i).symm

/-- Composition of two power lifts with coefficient transport is the lift of
the sum of the two exponents. -/
theorem subfieldCyclicPowerLift_mul (n m : ℕ) :
    (subfieldCyclicPowerLift K D ι b hj n : Matrix Index Index L) *
      (subfieldCyclicPowerLift K D ι b hj m : Matrix Index Index L).map (σ ^ n) =
        (subfieldCyclicPowerLift K D ι b hj (n + m) : Matrix Index Index L) := by
  let := localDivisionSubfieldLeftModule K D ι
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  let s := σ ^ (n + m)
  have hsurj : Function.Surjective (fun x : D => s ∘ b.equivFun x) :=
    (Equiv.piCongrRight (fun _ : Index => s.toEquiv)).surjective.comp b.equivFun.surjective
  obtain ⟨x, rfl⟩ := hsurj v
  have hvec : s ∘ b.equivFun x = (σ ^ n) ∘ ((σ ^ m) ∘ b.repr x) := by
    funext i
    change (σ ^ (n + m)) (b.repr x i) = (σ ^ n) ((σ ^ m) (b.repr x i))
    rw [pow_add, AlgEquiv.mul_apply]
  dsimp only
  rw [← Matrix.mulVec_mulVec, hvec, map_mulVec_equiv, subfieldCyclicPowerLift_mulVec,
    subfieldCyclicPowerLift_mulVec, ← hvec]
  rw [show (j : D) ^ n * ((j : D) ^ m * x) = (j : D) ^ (n + m) * x by
    rw [pow_add, mul_assoc]]
  exact (subfieldCyclicPowerLift_mulVec K D ι b hj (n + m) x).symm

variable [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The power lift induces exactly the canonical semilinear action transported
through the opposite splitting chart. -/
theorem subfieldCyclicPowerLift_chartAction (n : ℕ) (X : Matrix Index Index L) :
    (CentralSimple.splittingChartIndexAction (subfieldOppositeSplittingChart K D ι b)).act (σ ^ n) X =
      (subfieldCyclicPowerLift K D ι b hj n : Matrix Index Index L) * X.map (σ ^ n) *
        (((subfieldCyclicPowerLift K D ι b hj n)⁻¹ : GL Index L) : Matrix Index Index L) := by
  let := localDivisionSubfieldLeftModule K D ι
  let e := subfieldOppositeSplittingChart K D ι b
  let P := subfieldCyclicPowerLift K D ι b hj n
  let s := σ ^ n
  obtain ⟨y, rfl⟩ := e.surjective X
  rw [CentralSimple.splittingChartIndexAction_apply]
  have hMul : e (CentralSimple.tensorCoefficientMap s y) * (P : Matrix Index Index L) =
      (P : Matrix Index Index L) * (e y).map s := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      have hm : (e y + e z).map s = (e y).map s + (e z).map s := by
        ext i k
        exact s.map_add (e y i k) (e z i k)
      simp only [map_add, hm, add_mul, mul_add, hy, hz]
    | tmul a r =>
      rw [CentralSimple.tensorCoefficientMap_tmul]
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      have hsurj : Function.Surjective (fun x : D => s ∘ b.equivFun x) :=
        (Equiv.piCongrRight (fun _ : Index => s.toEquiv)).surjective.comp b.equivFun.surjective
      obtain ⟨x, rfl⟩ := hsurj v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change e (s a ⊗ₜ[K] r) *ᵥ ((P : Matrix Index Index L) *ᵥ (s ∘ b.repr x)) =
        (P : Matrix Index Index L) *ᵥ ((e (a ⊗ₜ[K] r)).map s *ᵥ (s ∘ b.repr x))
      rw [map_mulVec_equiv, subfieldCyclicPowerLift_mulVec, subfieldOppositeSplittingChart_tmul_mulVec,
        subfieldOppositeSplittingChart_tmul_mulVec, subfieldCyclicPowerLift_mulVec]
      apply congrArg (fun w : D => (b.repr w : Vec))
      calc
        ι (s a) * ((j : D) ^ n * x) * r.unop = (((j : D) ^ n * ι a) * x) * r.unop := by
          rw [implementingUnit_pow_mul K D ι hj]
          simp only [mul_assoc, s]
        _ = _ := by simp only [mul_assoc]
  calc
    e (CentralSimple.tensorCoefficientMap s y) =
        (e (CentralSimple.tensorCoefficientMap s y) * (P : Matrix Index Index L)) *
          ((P⁻¹ : GL Index L) : Matrix Index Index L) := by
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    _ = _ := by rw [hMul]

end Langlands.CentralDivision
