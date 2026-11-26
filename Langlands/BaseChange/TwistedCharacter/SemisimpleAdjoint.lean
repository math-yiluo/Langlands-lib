import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Semisimple

/-! # Conjugation by a semisimple linear automorphism -/

noncomputable section

namespace Langlands.BaseChange

open Module Polynomial

variable {F V : Type*} [Field F] [PerfectField F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

local notation "A" => End F V

omit [PerfectField F] in
private theorem isSemisimple_unit_inv (u : Aˣ) (hu : Module.End.IsSemisimple u.val) :
    Module.End.IsSemisimple (u⁻¹ : Aˣ).val := by
  let p := minpoly F u.val
  have hconst : p.coeff 0 ≠ 0 :=
    LinearMap.minpoly_coeff_zero_of_injective ((Module.End.isUnit_iff _).mp u.isUnit).injective
  have hcop : IsCoprime (X : F[X]) p :=
    irreducible_X.coprime_iff_not_dvd.mpr fun h => hconst (X_dvd_iff.mp h)
  obtain ⟨a, b, hab⟩ := hcop
  have h := congrArg (aeval u.val) hab
  simp only [map_add, map_mul, aeval_X, map_one, show aeval u.val p = 0 from minpoly.aeval _ _,
    mul_zero, add_zero] at h
  have he : (u⁻¹ : Aˣ).val = aeval u.val a := by
    rw [← one_mul (u⁻¹ : Aˣ).val, ← h, mul_assoc, Units.mul_inv, mul_one]
  rw [he]
  exact hu.aeval a

/-- Conjugation by a semisimple linear automorphism is semisimple on the endomorphism space. -/
theorem isSemisimple_conjugationOnEnd (u : Aˣ) (hu : Module.End.IsSemisimple u.val) :
    Module.End.IsSemisimple ((u.mulLeftLinearEquiv F A).trans
      (u⁻¹.mulRightLinearEquiv F)).toLinearMap := by
  let L := Algebra.lmul F A
  let e : Aᵐᵒᵖ ≃ₗ[F] A := (MulOpposite.opLinearEquiv (R := F) (M := A)).symm
  let R := (e.conjAlgEquiv F).toAlgHom.comp (Algebra.lmul F Aᵐᵒᵖ)
  let w := (u⁻¹ : Aˣ).val
  have hw := isSemisimple_unit_inv u hu
  have hL : Module.End.IsSemisimple (L u.val) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hu.minpoly_squarefree
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  have hR : Module.End.IsSemisimple (R (MulOpposite.op w)) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hw.minpoly_squarefree
    rw [aeval_algHom_apply, aeval_op_apply, minpoly.aeval, MulOpposite.op_zero, map_zero]
  have hcomm : Commute (L u.val) (R (MulOpposite.op w)) := by
    apply LinearMap.ext
    intro a
    change u.val * (a * w) = (u.val * a) * w
    rw [mul_assoc]
  have hss := Module.End.IsSemisimple.mul_of_commute hcomm hL hR
  convert hss using 1
  apply LinearMap.ext
  intro a
  change (u.val * a) * w = u.val * (a * w)
  exact mul_assoc _ _ _

end Langlands.BaseChange
