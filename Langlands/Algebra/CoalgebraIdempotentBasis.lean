import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Group-like bases from orthogonal idempotents in the convolution dual -/

noncomputable section

universe u v

open Coalgebra WithConv Module
open scoped TensorProduct

namespace Langlands.CoalgebraIdempotentBasis

variable {R : Type u} [CommRing R]
  {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]
  [Module.Free R C] [Module.Finite R C]

/-- The primal basis dual to a finite basis of the convolution dual. -/
def primalBasis {ι : Type*} [Fintype ι]
    (b : Basis ι R (WithConv (C →ₗ[R] R))) : Basis ι R C := by
  classical
  exact ((b.map (WithConv.linearEquiv R (C →ₗ[R] R))).dualBasis).map
    (Module.evalEquiv R C).symm

omit [Coalgebra R C] in
@[simp]
theorem apply_primalBasis {ι : Type*} [Fintype ι]
    (b : Basis ι R (WithConv (C →ₗ[R] R)))
    (f : WithConv (C →ₗ[R] R)) (i : ι) : f (primalBasis b i) = b.repr f i := by
  classical
  change f.ofConv ((Module.evalEquiv R C).symm
    ((b.map (WithConv.linearEquiv R (C →ₗ[R] R))).dualBasis i)) = _
  rw [Module.apply_evalEquiv_symm_apply, Basis.dualBasis_apply]
  rfl

omit [Coalgebra R C] in
@[simp]
theorem primalBasis_coord {ι : Type*} [Fintype ι]
    (b : Basis ι R (WithConv (C →ₗ[R] R))) (i : ι) :
    (primalBasis b).coord i = (b i).ofConv := by
  classical
  apply (primalBasis b).ext
  intro j
  simp [Basis.coord_apply, Finsupp.single_apply, eq_comm]

/-- Convolution is the dual of the actual comultiplication, expressed in
finite primal tensor coordinates. -/
theorem tensor_coord_comul {ι : Type*} [Fintype ι]
    (b : Basis ι R (WithConv (C →ₗ[R] R))) (x : C) (i j : ι) :
    ((primalBasis b).tensorProduct (primalBasis b)).repr (comul x) (i, j) =
      (b i * b j) x := by
  have h : ((primalBasis b).tensorProduct (primalBasis b)).coord (i, j) =
      (LinearMap.mul' R R).comp (TensorProduct.map (b i).ofConv (b j).ofConv) := by
    ext y z
    change ((primalBasis b).tensorProduct (primalBasis b)).coord (i, j)
      (y ⊗ₜ[R] z) = _
    rw [Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply]
    change (primalBasis b).coord j z • (primalBasis b).coord i y =
      (b i).ofConv y * (b j).ofConv z
    rw [primalBasis_coord, primalBasis_coord]
    exact mul_comm _ _
  exact congrArg (fun f : C ⊗[R] C →ₗ[R] R => f (comul x)) h

omit [Module.Free R C] [Module.Finite R C] in
/-- The unit has all coordinates one in an orthogonal idempotent basis. -/
theorem repr_one {ι : Type*} [Fintype ι]
    (b : Basis ι R (WithConv (C →ₗ[R] R))) (hb : OrthogonalIdempotents b) (i : ι) :
    b.repr 1 i = 1 := by
  classical
  have hmul (f : WithConv (C →ₗ[R] R)) : b i * f = b.repr f i • b i := by
    conv_lhs => rw [← b.sum_repr f]
    rw [Finset.mul_sum]
    simp [mul_smul_comm, hb.mul_eq]
  have h := congrArg (fun f : WithConv (C →ₗ[R] R) => b.repr f i) (hmul 1)
  simpa using h.symm

/-- An orthogonal idempotent basis of the convolution dual gives an actual
basis of group-like elements of the coalgebra. -/
theorem isGroupLike_primalBasis {ι : Type*} [Fintype ι]
    (b : Basis ι R (WithConv (C →ₗ[R] R))) (hb : OrthogonalIdempotents b) (k : ι) :
    IsGroupLikeElem R (primalBasis b k) := by
  classical
  constructor
  · change (1 : WithConv (C →ₗ[R] R)) (primalBasis b k) = 1
    rw [apply_primalBasis, repr_one b hb]
  · apply ((primalBasis b).tensorProduct (primalBasis b)).repr.injective
    ext ⟨i, j⟩
    rw [tensor_coord_comul, hb.mul_eq]
    by_cases hik : i = k
    · subst i
      by_cases hjk : j = k
      · subst j
        simp
      · simp [hjk, Ne.symm hjk, Basis.repr_self, smul_eq_mul]
    · by_cases hij : i = j
      · subst j
        simp [hik, Ne.symm hik, Basis.repr_self, smul_eq_mul]
      · simp [hik, hij, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]

end Langlands.CoalgebraIdempotentBasis
