import Langlands.BaseChange.CyclicAlgebraTrace
import Langlands.BaseChange.WeylTorusLie
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Split cyclic coordinates on matrix spaces -/

noncomputable section

namespace Langlands.BaseChange

open scoped TensorProduct
open Fin.NatCast

universe u v w

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {K : Type w} [Field K] [Algebra F K] {l n : ℕ}

local notation "MF" => Matrix (Fin n) (Fin n) F
local notation "ME" => Matrix (Fin n) (Fin n) E
local notation "MK" => Matrix (Fin n) (Fin n) K

/-- Distributing scalar extension over the matrix entries. -/
def matrixScalarExtension : (K ⊗[F] MF) ≃ₗ[K] MK :=
  (TensorProduct.piRight F K K (fun _ : Fin n => Fin n → F)).trans
    (LinearEquiv.piCongrRight fun _ => (TensorProduct.piRight F K K (fun _ : Fin n => F)).trans
      (LinearEquiv.piCongrRight fun _ => TensorProduct.AlgebraTensorModule.rid F K K))

@[simp]
theorem matrixScalarExtension_tmul (a : K) (x : MF) (p q : Fin n) :
    matrixScalarExtension (a ⊗ₜ[F] x) p q = a * algebraMap F K (x p q) := by
  change x p q • a = _
  rw [Algebra.smul_def, mul_comm]

private def rearrangeMatrixCoordinates :
    (Fin n → Fin n → Fin l → K) ≃ₗ[K] (Fin l → MK) where
  toFun x i p q := x p q i
  invFun x p q i := x i p q
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Splitting the coefficient algebra also splits matrices into cyclic copies. -/
def cyclicMatrixScalarExtension (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) :
    (K ⊗[F] ME) ≃ₗ[K] (Fin l → MK) :=
  (TensorProduct.piRight F K K (fun _ : Fin n => Fin n → E)).trans
    ((LinearEquiv.piCongrRight fun _ =>
      (TensorProduct.piRight F K K (fun _ : Fin n => E)).trans
        (LinearEquiv.piCongrRight fun _ => e.toLinearEquiv)).trans rearrangeMatrixCoordinates)

/-- The coefficient homomorphism obtained by evaluating one split coordinate. -/
def cyclicCoordinate (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) (i : Fin l) : E →ₐ[F] K :=
  (((Pi.evalAlgHom K (fun _ : Fin l => K) i).comp e.toAlgHom).restrictScalars F).comp
    Algebra.TensorProduct.includeRight

theorem cyclicCoordinate_apply (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) (i : Fin l) (x : E) :
    cyclicCoordinate e i x = e (1 ⊗ₜ[F] x) i := rfl

theorem cyclicCoordinate_shift (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) (σ : E ≃ₐ[F] E)
    (he : ∀ x j, e (tensorFactorAut K σ x) j = e x (finRotate l j)) (i : Fin l) (x : E) :
    cyclicCoordinate e i (σ x) = cyclicCoordinate e (finRotate l i) x := by
  simpa only [cyclicCoordinate_apply, tensorFactorAut_tmul] using he (1 ⊗ₜ[F] x) i

theorem cyclicCoordinate_pow (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K)) (σ : E ≃ₐ[F] E)
    (he : ∀ x j, e (tensorFactorAut K σ x) j = e x (finRotate l j))
    (i : Fin l) (k : ℕ) (x : E) :
    haveI := i.neZero
    cyclicCoordinate e i ((σ ^ k) x) = cyclicCoordinate e (i + (k : Fin l)) x := by
  let : NeZero l := i.neZero
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, cyclicCoordinate_shift e σ he, ih, finRotate_apply,
      Nat.cast_succ, add_right_comm, add_assoc]

@[simp]
theorem cyclicMatrixScalarExtension_tmul (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K))
    (a : K) (x : ME) (i : Fin l) (p q : Fin n) :
    cyclicMatrixScalarExtension e (a ⊗ₜ[F] x) i p q = a * cyclicCoordinate e i (x p q) := by
  change e (a ⊗ₜ[F] (x p q)) i = _
  rw [show a ⊗ₜ[F] (x p q) = a • ((1 : K) ⊗ₜ[F] (x p q)) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
  rfl

/-- The ordered norm becomes the product of the matrices in the split
coordinates numbered from zero. -/
theorem prod_splitCoordinates_units {σ : E ≃ₐ[F] E} (hσ : IsCyclicAlgebra σ l)
    (e : (K ⊗[F] E) ≃ₐ[K] (Fin l → K))
    (he : ∀ x j, e (tensorFactorAut K σ x) j = e x (finRotate l j))
    (δ : GeneralLinear n E) {γ : GeneralLinear n F}
    (hδ : cyclicNorm σ l δ = baseChange F E n γ) :
    (List.ofFn (fun i : Fin l => Matrix.GeneralLinearGroup.map (cyclicCoordinate e i).toRingHom δ)).prod =
      baseChange F K n γ := by
  let : NeZero l := ⟨hσ.pos.ne'⟩
  let c₀ := cyclicCoordinate e (0 : Fin l)
  have hmap : Matrix.GeneralLinearGroup.map c₀.toRingHom (baseChange F E n γ) =
      baseChange F K n γ := by
    apply Units.ext
    exact Matrix.ext fun j k => c₀.commutes (γ.val j k)
  rw [← hmap, ← hδ, cyclicNorm, map_list_prod, List.map_map]
  have hrange : (List.finRange l).map (fun i : Fin l => (i : ℕ)) = List.range l := by simp
  rw [← hrange, List.map_map, List.ofFn_eq_map]
  congr 1
  apply List.map_congr_left
  intro i _
  apply Units.ext
  refine Matrix.ext fun j k => ?_
  change cyclicCoordinate e i (δ.val j k) =
    cyclicCoordinate e 0 ((σ ^ (i : ℕ)) (δ.val j k))
  rw [cyclicCoordinate_pow e σ he]
  have hi : ((i : ℕ) : Fin l) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [zero_add, hi]

end Langlands.BaseChange
