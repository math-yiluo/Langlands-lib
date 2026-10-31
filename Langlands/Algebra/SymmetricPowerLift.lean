import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-! # The linear universal property of actual symmetric tensor powers -/

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Algebra.SymmetricTensors

universe u

variable {R ι : Type u} {M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

private theorem lift_compatible (f : MultilinearMap R (fun _ : ι => M) N)
    (hsym : ∀ (e : Equiv.Perm ι) (x : ι → M), f (x ∘ e) = f x) :
    addConGen (SymmetricPower.Rel R ι M) ≤
      AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.mpr
  rintro a b ⟨e, x⟩
  change PiTensorProduct.lift f (PiTensorProduct.tprod R x) =
    PiTensorProduct.lift f (PiTensorProduct.tprod R (x ∘ e))
  simpa using (hsym e x).symm

/-- Descend a symmetric multilinear map through the actual symmetric tensor
quotient. -/
def lift (f : MultilinearMap R (fun _ : ι => M) N)
    (hsym : ∀ (e : Equiv.Perm ι) (x : ι → M), f (x ∘ e) = f x) :
    Sym[R] ι M →ₗ[R] N where
  __ := AddCon.lift _ (PiTensorProduct.lift f).toAddMonoidHom (lift_compatible f hsym)
  map_smul' r a := by
    induction a using AddCon.induction_on with
    | _ a =>
      change PiTensorProduct.lift f (r • a) = r • PiTensorProduct.lift f a
      exact map_smul _ _ _

@[simp]
theorem lift_mk (f : MultilinearMap R (fun _ : ι => M) N)
    (hsym : ∀ (e : Equiv.Perm ι) (x : ι → M), f (x ∘ e) = f x)
    (a : ⨂[R] (_ : ι), M) :
    lift f hsym (SymmetricPower.mk R ι M a) = PiTensorProduct.lift f a := rfl

@[simp]
theorem lift_tprod (f : MultilinearMap R (fun _ : ι => M) N)
    (hsym : ∀ (e : Equiv.Perm ι) (x : ι → M), f (x ∘ e) = f x) (x : ι → M) :
    lift f hsym (SymmetricPower.tprod R x) = f x :=
  PiTensorProduct.lift.tprod (φ := f) x

/-- Linear maps out of the actual symmetric tensor power agree when they agree
on all symmetric pure tensors. -/
theorem linearMap_ext {f g : Sym[R] ι M →ₗ[R] N}
    (h : ∀ x : ι → M, f (SymmetricPower.tprod R x) = g (SymmetricPower.tprod R x)) :
    f = g :=
  LinearMap.ext_on_range (SymmetricPower.span_tprod_eq_top R ι M) h

theorem lift_unique (f : MultilinearMap R (fun _ : ι => M) N)
    (hsym : ∀ (e : Equiv.Perm ι) (x : ι → M), f (x ∘ e) = f x)
    (g : Sym[R] ι M →ₗ[R] N)
    (hg : ∀ x : ι → M, g (SymmetricPower.tprod R x) = f x) :
    g = lift f hsym :=
  linearMap_ext fun x => (hg x).trans (lift_tprod f hsym x).symm

end Langlands.Algebra.SymmetricTensors
