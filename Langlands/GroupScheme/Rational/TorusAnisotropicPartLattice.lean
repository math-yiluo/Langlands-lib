import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Integral invariants for the anisotropic part of a torus -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.TorusAnisotropicPart

open scoped BigOperators

variable {Γ : Type u} [Group Γ] [Fintype Γ]
  {M : Type v} [AddCommGroup M]
  (ρ : Representation ℤ Γ M)

/-- The difference map has the invariant lattice as its full integral kernel. -/
def differenceMap : M →ₗ[ℤ] (Γ → M) where
  toFun x g := ρ g x - x
  map_add' x y := by
    ext g
    change ρ g (x + y) - (x + y) = (ρ g x - x) + (ρ g y - y)
    rw [map_add]
    abel
  map_smul' n x := by
    ext g
    change ρ g (n • x) - n • x = n • (ρ g x - x)
    simp only [map_smul, smul_sub]

omit [Fintype Γ] in
theorem differenceMap_ker : (differenceMap ρ).ker = ρ.invariants := by
  ext x
  simp only [LinearMap.mem_ker, differenceMap, LinearMap.coe_mk, AddHom.coe_mk,
    funext_iff, Pi.zero_apply, sub_eq_zero, Representation.mem_invariants]

omit [Fintype Γ] in
/-- The invariants are saturated: their integral quotient is again free. -/
theorem free_quotient_invariants [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.Free ℤ (M ⧸ ρ.invariants) := by
  let e : (M ⧸ ρ.invariants) ≃ₗ[ℤ] LinearMap.range (differenceMap ρ) :=
    ((Submodule.quotEquivOfEq _ _ (differenceMap_ker ρ).symm).trans
      (differenceMap ρ).quotKerEquivRange).toAddEquiv.toIntLinearEquiv
  exact Module.Free.of_equiv e.symm

/-- The integral orbit sum always belongs to the invariant lattice. -/
theorem sum_mem_invariants (x : M) : (∑ g : Γ, ρ g x) ∈ ρ.invariants := by
  intro h
  simp only [map_sum]
  calc
    ∑ g : Γ, ρ h (ρ g x) = ∑ g : Γ, ρ (h * g) x := by
      congr 1
      ext g
      exact (congrArg (fun f : Module.End ℤ M => f x) (ρ.map_mul h g)).symm
    _ = ∑ g : Γ, ρ g x := Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)

end Langlands.GroupScheme.TorusAnisotropicPart
