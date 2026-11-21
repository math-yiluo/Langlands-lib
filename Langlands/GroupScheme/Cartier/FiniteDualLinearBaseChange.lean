import Langlands.GroupScheme.Cartier.FiniteDualAlgebra
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Scalar extension of the underlying finite projective Cartier dual -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1100000

open TensorProduct Module

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

private def extendFunctional : (M →ₗ[R] S) ≃ₗ[S] Module.Dual S (S ⊗[R] M) where
  toFun f := TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton S _ f)
  invFun α := (α.restrictScalars R).comp (TensorProduct.mk R S M 1)
  left_inv f := by
    ext x
    change (1 : S) • f x = f x
    exact one_smul _ _
  right_inv α := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    change s • α (1 ⊗ₜ[R] x) = α (s ⊗ₜ[R] x)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  map_add' f g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    change s • (f x + g x) = s • f x + s • g x
    exact smul_add _ _ _
  map_smul' t f := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    change s • (t • f x) = t • (s • f x)
    exact smul_comm _ _ _

variable [Module.Finite R M] [Module.Projective R M]

private def dualToHom :=
  (TensorProduct.comm R S (Module.Dual R M)).trans (dualTensorHomEquiv R M S)

/-- The actual linear dual of a finite projective module commutes with scalar extension. -/
def moduleDualBaseChange : S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) where
  __ := (dualToHom R S M).toEquiv.trans (extendFunctional R S M).toEquiv
  map_add' f g := by
    change extendFunctional R S M (dualToHom R S M (f + g)) =
      extendFunctional R S M (dualToHom R S M f) + extendFunctional R S M (dualToHom R S M g)
    rw [map_add, map_add]
  map_smul' s z := by
    have hz : dualToHom R S M (s • z) = s • dualToHom R S M z := by
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul t f =>
        ext x
        change f x • (s • t) = s • (f x • t)
        exact smul_comm _ _ _
    change extendFunctional R S M (dualToHom R S M (s • z)) =
      s • extendFunctional R S M (dualToHom R S M z)
    rw [hz, map_smul]

@[simp] theorem moduleDualBaseChange_tmul_apply (s t : S) (f : Module.Dual R M) (x : M) :
    moduleDualBaseChange R S M (s ⊗ₜ[R] f) (t ⊗ₜ[R] x) = s * t * algebraMap R S (f x) := by
  change t • (f x • s) = _
  rw [smul_eq_mul, Algebra.smul_def]
  ac_rfl

/-- The equivalence for the convolution dual, retaining its underlying module. -/
def linearDualBaseChange : S ⊗[R] Dual R M ≃ₗ[S] Dual S (S ⊗[R] M) :=
  (LinearEquiv.baseChange R S _ _ (WithConv.linearEquiv R (Module.Dual R M))).trans
    ((moduleDualBaseChange R S M).trans (WithConv.linearEquiv S _).symm)

@[simp] theorem linearDualBaseChange_tmul_apply (s t : S) (f : Dual R M) (x : M) :
    linearDualBaseChange R S M (s ⊗ₜ[R] f) (t ⊗ₜ[R] x) = s * t * algebraMap R S (f x) :=
  moduleDualBaseChange_tmul_apply R S M s t f.ofConv x

/-- The actual finite projective dual has the same rank on every stalk. -/
theorem rankAtStalk_dual (x : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Dual R M) x = Module.rankAtStalk (R := R) M x := by
  let T := x.asIdeal.ResidueField
  have e := (linearDualBaseChange R T M).trans (WithConv.linearEquiv T _)
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq, e.finrank_eq, Subspace.dual_finrank_eq]

end Langlands.GroupScheme.Cartier.FiniteDual
