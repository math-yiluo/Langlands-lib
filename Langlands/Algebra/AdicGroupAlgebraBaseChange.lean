import Langlands.Algebra.AdicGroupAlgebra
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-! # Adic effectivity from actual scalar-extended bialgebra maps -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.AdicGroupAlgebraBaseChange

attribute [local instance] Classical.propDecidable

variable {A : Type u} [CommRing A] {C : Type v} [CommRing C] [Bialgebra A C]
variable {M : Type w} [AddCommGroup M]
variable {Q : Type z} [CommRing Q] [Algebra A Q]

/-- Restrict a scalar-extended bialgebra map to the original algebra. -/
def restrict (F : (Q ⊗[A] C) →ₐc[Q] AddMonoidAlgebra Q M) :
    C →ₐ[A] AddMonoidAlgebra Q M :=
  (F.toAlgHom.restrictScalars A).comp Algebra.TensorProduct.includeRight

@[simp] theorem restrict_apply (F : (Q ⊗[A] C) →ₐc[Q] AddMonoidAlgebra Q M) (x : C) :
    restrict F x = F (1 ⊗ₜ[A] x) := rfl

/-- Compare the coefficient pairing with the scalar-extended tensor map. -/
theorem tensorCoefficient_restrict
    (F : (Q ⊗[A] C) →ₐc[Q] AddMonoidAlgebra Q M) (t : C ⊗[A] C) (m k : M) :
    AdicDiagonalAlgebraization.tensorCoefficient
        (AdicGroupAlgebra.coefficientFunction (restrict F)) m k t =
      (AddMonoidAlgebra.tensorEquiv Q
        (TensorProduct.map F.toLinearMap F.toLinearMap
          (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm A Q A Q Q Q C C
            ((1 ⊗ₜ[Q] (1 : Q)) ⊗ₜ[A] t)))).coeff (m, k) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp; rfl
  | add t s ht hs =>
      simp only [map_add, TensorProduct.tmul_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, ht, hs]

/-- A genuine bialgebra map satisfies the diagonal coefficient equations. -/
theorem restrict_diagonal
    (F : (Q ⊗[A] C) →ₐc[Q] AddMonoidAlgebra Q M) (x : C) (m k : M) :
    AdicDiagonalAlgebraization.tensorCoefficient
        (AdicGroupAlgebra.coefficientFunction (restrict F)) m k
        (Coalgebra.comul (R := A) x) =
      if m = k then (restrict F x).coeff m else 0 := by
  rw [tensorCoefficient_restrict]
  have heq := CoalgHomClass.map_comp_comul_apply F (1 ⊗ₜ[A] x)
  simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply] at heq
  change TensorProduct.map F.toLinearMap F.toLinearMap
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm A Q A Q Q Q C C
      ((1 ⊗ₜ[Q] (1 : Q)) ⊗ₜ[A] Coalgebra.comul (R := A) x)) =
        Coalgebra.comul (R := Q) (F (1 ⊗ₜ[A] x)) at heq
  rw [heq, AdicGroupAlgebra.comul_coeff]
  rfl

/-- Its counit equation restricts to the base-ring counit. -/
theorem restrict_counit
    (F : (Q ⊗[A] C) →ₐc[Q] AddMonoidAlgebra Q M) (x : C) :
    Coalgebra.counit (R := Q) (restrict F x) =
      algebraMap A Q (Coalgebra.counit (R := A) x) := by
  rw [restrict_apply, CoalgHomClass.counit_comp_apply]
  simp [Algebra.algebraMap_eq_smul_one]

variable (I : Ideal A)

/-- A compatible family of genuine bialgebra maps on scalar extensions. -/
structure System where
  map (n : ℕ) : ((A ⧸ I ^ n) ⊗[A] C) →ₐc[A ⧸ I ^ n] AddMonoidAlgebra (A ⧸ I ^ n) M
  compatible : ∀ {n k : ℕ} (h : n ≤ k) (x : C) (m : M),
    Ideal.Quotient.factorPow I h ((map k (1 ⊗ₜ[A] x)).coeff m) =
      (map n (1 ⊗ₜ[A] x)).coeff m

namespace System

variable {I} (f : System I (C := C) (M := M))

/-- A system indexed by positive quotient powers extends over the zero quotient. -/
def ofSucc
    (F : (n : ℕ) → ((A ⧸ I ^ (n + 1)) ⊗[A] C) →ₐc[A ⧸ I ^ (n + 1)]
      AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M)
    (hF : ∀ (n : ℕ) (x : C) (m : M),
      Ideal.Quotient.factorPow I (n + 1).le_succ ((F (n + 1) (1 ⊗ₜ[A] x)).coeff m) =
        (F n (1 ⊗ₜ[A] x)).coeff m) : System I (C := C) (M := M) := by
  let g : (n : ℕ) → ((A ⧸ I ^ n) ⊗[A] C) →ₐc[A ⧸ I ^ n]
      AddMonoidAlgebra (A ⧸ I ^ n) M
    | 0 => (Bialgebra.unitBialgHom (A ⧸ I ^ 0) _).comp
        (Bialgebra.counitBialgHom (A ⧸ I ^ 0) _)
    | n + 1 => F n
  refine ⟨g, ?_⟩
  intro n k h x m
  symm
  refine Ideal.Quotient.eq_factor_of_eq_factor_succ
    (fun _ _ h => Ideal.pow_le_pow_right h)
    (fun j => (g j (1 ⊗ₜ[A] x)).coeff m) ?_ h
  intro j
  cases j with
  | zero =>
      have : Subsingleton (A ⧸ I ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact Subsingleton.elim _ _
  | succ j => exact (hF j x m).symm

@[simp] theorem ofSucc_map
    (F : (n : ℕ) → ((A ⧸ I ^ (n + 1)) ⊗[A] C) →ₐc[A ⧸ I ^ (n + 1)]
      AddMonoidAlgebra (A ⧸ I ^ (n + 1)) M)
    (hF : ∀ (n : ℕ) (x : C) (m : M),
      Ideal.Quotient.factorPow I (n + 1).le_succ ((F (n + 1) (1 ⊗ₜ[A] x)).coeff m) =
        (F n (1 ⊗ₜ[A] x)).coeff m) (n : ℕ) :
    (ofSucc F hF).map (n + 1) = F n := rfl

/-- The coefficient equations of a genuine quotient system require no extra premises. -/
def toAlgebraSystem : AdicGroupAlgebra.System I (Coalgebra.comul (R := A) (A := C))
    (M := M) where
  map n := restrict (f.map n)
  compatible h x m := f.compatible h x m
  diagonal n x m k := restrict_diagonal (f.map n) x m k

variable [IsAdicComplete I A] [IsNoetherianRing A]

/-- Algebraize the genuine scalar-extended bialgebra maps. -/
def lift : C →ₐc[A] AddMonoidAlgebra A M :=
  AdicGroupAlgebra.liftBialgHom I f.toAlgebraSystem
    (fun n x => restrict_counit (f.map n) x)

@[simp] theorem reduce_lift (n : ℕ) (x : C) :
    AdicGroupAlgebra.reduce I n (f.lift x) = f.map n (1 ⊗ₜ[A] x) :=
  AdicGroupAlgebra.reduce_liftBialgHom I f.toAlgebraSystem _ n x

/-- Uniqueness of the algebraized bialgebra map on the original algebra. -/
theorem lift_unique (g : C →ₐc[A] AddMonoidAlgebra A M)
    (hg : ∀ (n : ℕ) (x : C), AdicGroupAlgebra.reduce I n (g x) =
      f.map n (1 ⊗ₜ[A] x)) : g = f.lift :=
  AdicGroupAlgebra.liftBialgHom_unique I f.toAlgebraSystem _ g hg

end System

/-- The ordinary scalar extension of an algebra map, using the standard group-algebra
scalar-extension equivalence on its target. -/
def extend (g : C →ₐ[A] AddMonoidAlgebra A M) :
    (Q ⊗[A] C) →ₐ[Q] AddMonoidAlgebra Q M :=
  (AddMonoidAlgebra.scalarTensorEquiv A Q (M := M)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id Q Q) g)

@[simp] theorem extend_tmul (g : C →ₐ[A] AddMonoidAlgebra A M) (a : Q) (x : C) :
    extend (Q := Q) g (a ⊗ₜ[A] x) =
      a • AddMonoidAlgebra.mapAlgHom M (Algebra.ofId A Q) (g x) := by
  simp [extend]

/-- The lifted map realizes the full scalar-extended maps, not just their restrictions. -/
theorem System.extend_lift [IsAdicComplete I A] [IsNoetherianRing A]
    (f : System I (C := C) (M := M)) (n : ℕ) :
    extend (Q := A ⧸ I ^ n) f.lift.toAlgHom = (f.map n).toAlgHom := by
  apply AlgHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
      rw [extend_tmul]
      change a • AdicGroupAlgebra.reduce I n (f.lift x) = f.map n (a ⊗ₜ[A] x)
      rw [f.reduce_lift]
      rw [show a ⊗ₜ[A] x = a • (1 ⊗ₜ[A] x) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact (map_smul (f.map n) a (1 ⊗ₜ[A] x)).symm
  | add t s ht hs => simp only [map_add, ht, hs]

end Langlands.AdicGroupAlgebraBaseChange
