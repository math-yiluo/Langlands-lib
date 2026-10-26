import Langlands.GroupScheme.MuCoordinateAlgebraStatement
import Mathlib.RingTheory.Etale.StandardEtale

/-! # Finite étaleness of the roots-of-unity coordinate algebra -/

universe u

namespace Langlands.GroupScheme

open Polynomial

set_option backward.isDefEq.respectTransparency false in
/-- The actual roots-of-unity coordinate quotient is finite and étale when the
positive index is a unit in the coefficient ring. -/
theorem muCoordinateAlgebra : MuCoordinateAlgebraStatement.{u} := by
  intro A n hn hu
  have hf : ((X : A[X]) ^ n - 1).Monic := by
    simpa using monic_X_pow_sub_C (1 : A) (Nat.ne_of_gt hn)
  refine ⟨hf.finite_adjoinRoot, ?_⟩
  obtain ⟨m, hm⟩ := hu.exists_right_inv
  let P : StandardEtalePair A :=
    { f := X ^ n - 1
      monic_f := hf
      g := 1
      cond := by
        refine ⟨C m * X, -1, 0, ?_⟩
        simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, pow_zero]
        have hX : (X : A[X]) ^ (n - 1) * X = X ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        calc
          C (n : A) * X ^ (n - 1) * (C m * X) + (X ^ n - 1) * (-1) =
              (C (n : A) * C m) * (X ^ (n - 1) * X) - (X ^ n - 1) := by ring
          _ = 1 := by rw [← C_mul, hm, C_1, hX]; ring }
  let toQuotient : P.Ring →ₐ[A] AdjoinRoot ((X : A[X]) ^ n - 1) :=
    P.lift (AdjoinRoot.root _) ⟨by
      change aeval (AdjoinRoot.root P.f) P.f = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by simp [P]⟩
  let fromQuotient : AdjoinRoot ((X : A[X]) ^ n - 1) →ₐ[A] P.Ring :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) P.X P.hasMap_X.1
  have h₁ : fromQuotient.comp toQuotient = AlgHom.id A P.Ring := by
    apply P.hom_ext
    simp [toQuotient, fromQuotient]
  have h₂ : toQuotient.comp fromQuotient =
      AlgHom.id A (AdjoinRoot ((X : A[X]) ^ n - 1)) := by
    apply AdjoinRoot.algHom_ext
    simp [toQuotient, fromQuotient]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom toQuotient fromQuotient h₂ h₁)

end Langlands.GroupScheme
