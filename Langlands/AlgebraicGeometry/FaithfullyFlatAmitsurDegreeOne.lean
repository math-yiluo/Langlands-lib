import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Abel

/-! # Degree-one faithfully flat Amitsur exactness

The right-associated tensor complex has differentials given by alternating
insertion of the algebra unit. Multiplication contracts its scalar extension.
-/

universe u v w

open TensorProduct

namespace Langlands.AlgebraicGeometry.AmitsurDegreeOne

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (N : Type w) [AddCommGroup N] [Module A N]

/-- Insert the algebra unit on the left. -/
def insertOne : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1

@[simp] theorem insertOne_apply (n : N) : insertOne A B N n = 1 ⊗ₜ[A] n := rfl

/-- The first alternating insertion differential. -/
def d0 : B ⊗[A] N →ₗ[A] B ⊗[A] (B ⊗[A] N) :=
  insertOne A B (B ⊗[A] N) - (insertOne A B N).lTensor B

/-- The second alternating insertion differential. -/
def d1 : B ⊗[A] (B ⊗[A] N) →ₗ[A] B ⊗[A] (B ⊗[A] (B ⊗[A] N)) :=
  insertOne A B (B ⊗[A] (B ⊗[A] N)) -
    (insertOne A B (B ⊗[A] N)).lTensor B +
    ((insertOne A B N).lTensor B).lTensor B

@[simp] theorem d0_tmul (b : B) (n : N) :
    d0 A B N (b ⊗ₜ[A] n) =
      1 ⊗ₜ[A] (b ⊗ₜ[A] n) - b ⊗ₜ[A] (1 ⊗ₜ[A] n) := rfl

@[simp] theorem d1_tmul (b c : B) (n : N) :
    d1 A B N (b ⊗ₜ[A] (c ⊗ₜ[A] n)) =
      1 ⊗ₜ[A] (b ⊗ₜ[A] (c ⊗ₜ[A] n)) -
        b ⊗ₜ[A] (1 ⊗ₜ[A] (c ⊗ₜ[A] n)) +
        b ⊗ₜ[A] (c ⊗ₜ[A] (1 ⊗ₜ[A] n)) := rfl

/-- Consecutive differentials compose to zero. -/
theorem d1_d0 (x : B ⊗[A] N) : d1 A B N (d0 A B N x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul b n => simp only [d0_tmul, map_sub, d1_tmul]; abel
  | add x y hx hy => simp [hx, hy]

variable {N}

/-- Multiply the first tensor factor into a compatible module. -/
def contraction (X : Type*) [AddCommGroup X] [Module A X] [Module B X]
    [IsScalarTower A B X] : B ⊗[A] X →ₗ[A] X :=
  TensorProduct.lift (Algebra.lsmul A A X : B →ₐ[A] Module.End A X).toLinearMap

@[simp] theorem contraction_tmul (X : Type*) [AddCommGroup X] [Module A X]
    [Module B X] [IsScalarTower A B X] (b : B) (x : X) :
    contraction A B X (b ⊗ₜ[A] x) = b • x := rfl

variable (N)

/-- The extended complex has an explicit contracting identity. -/
theorem contracting_identity (x : B ⊗[A] (B ⊗[A] (B ⊗[A] N))) :
    (d0 A B N).lTensor B (contraction A B (B ⊗[A] (B ⊗[A] N)) x) +
      contraction A B (B ⊗[A] (B ⊗[A] (B ⊗[A] N)))
        ((d1 A B N).lTensor B x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul b y =>
    induction y using TensorProduct.inductionOn with
    | tmul c z =>
      induction z using TensorProduct.inductionOn with
      | tmul d n =>
        simp only [contraction_tmul, LinearMap.lTensor_tmul, d0_tmul, d1_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_add,
          TensorProduct.tmul_sub, map_add, map_sub, mul_one]
        abel
      | add z z' hz hz' =>
        simp only [TensorProduct.tmul_add, map_add]
        rw [add_add_add_comm, hz, hz']
    | add y y' hy hy' =>
      simp only [TensorProduct.tmul_add, map_add]
      rw [add_add_add_comm, hy, hy']
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]

/-- Exactness after scalar extension, without a flatness assumption. -/
theorem baseChange_exact :
    Function.Exact ((d0 A B N).lTensor B) ((d1 A B N).lTensor B) := by
  intro x
  constructor
  · intro hx
    refine ⟨contraction A B (B ⊗[A] (B ⊗[A] N)) x, ?_⟩
    simpa [hx] using contracting_identity A B N x
  · rintro ⟨y, rfl⟩
    have hcomp : (d1 A B N).comp (d0 A B N) = 0 := by
      apply LinearMap.ext
      intro z
      exact d1_d0 A B N z
    rw [← LinearMap.lTensor_comp_apply, hcomp]
    simp

/-- Faithful flatness reflects degree-one exactness. -/
theorem exact [Module.FaithfullyFlat A B] : Function.Exact (d0 A B N) (d1 A B N) :=
  Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ (baseChange_exact A B N)

/-- Every degree-one cocycle is a coboundary. -/
theorem exists_primitive [Module.FaithfullyFlat A B]
    (x : B ⊗[A] (B ⊗[A] N)) (hx : d1 A B N x = 0) :
    ∃ y : B ⊗[A] N, d0 A B N y = x := (exact A B N x).mp hx

end Langlands.AlgebraicGeometry.AmitsurDegreeOne
