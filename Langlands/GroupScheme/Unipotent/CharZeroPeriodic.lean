import Langlands.Weil.Local.BlockSumParameter
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.Separable

/-!
# Periodic vectors of unipotent linear maps in characteristic zero

This internal linear algebra lemma is used to study the translation action on
the connected components of a unipotent algebraic group.
-/

noncomputable section

open Polynomial

namespace Langlands.GroupScheme.Unipotent

variable {k M : Type*} [Field k] [CharZero k] [AddCommGroup M] [Module k M]

/-- A unipotent endomorphism of finite order is the identity in characteristic zero. -/
theorem eq_one_of_isNilpotent_sub_one_of_pow_eq_one {f : Module.End k M} {n : ℕ}
    (hu : IsNilpotent (f - 1)) (hn : n ≠ 0) (hf : f ^ n = 1) : f = 1 := by
  have hss : (f - 1).IsSemisimple := by
    simpa using
      (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := (1 : k))).mpr
        (Langlands.BlockSumParameter.isSemisimple_of_pow_eq_one hn hf)
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hu hss)

/-- A periodic vector killed by a power of `f - 1` is fixed by `f`. Only the
given vector needs to satisfy a unipotence condition. -/
theorem apply_eq_self_of_periodic_of_pow_sub_one_eq_zero
    {f : Module.End k M} {x : M} {n m : ℕ}
    (hn : n ≠ 0) (hperiodic : (f ^ n) x = x)
    (hu : ((f - 1) ^ m) x = 0) : f x = x := by
  let p : Submodule k M := LinearMap.ker (f ^ n - 1)
  have hp : ∀ y ∈ p, f y ∈ p := by
    intro y hy
    change (f ^ n) y - y = 0 at hy
    change (f ^ n) (f y) - f y = 0
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply,
      sub_eq_zero.mp hy, sub_self]
  let F : Module.End k p := f.restrict hp
  have hF : F ^ n = 1 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change (((f.restrict hp) ^ n) y : M) = (y : M)
    rw [Module.End.pow_restrict]
    change (f ^ n) (y : M) = (y : M)
    have hy := y.property
    change (f ^ n) (y : M) - (y : M) = 0 at hy
    exact sub_eq_zero.mp hy
  have hx : x ∈ p := by
    change (f ^ n) x - x = 0
    rw [hperiodic, sub_self]
  let x' : p := ⟨x, hx⟩
  have hsub : ∀ y ∈ p, (f - 1) y ∈ p := by
    intro y hy
    exact p.sub_mem (hp y hy) hy
  have hrestrict : F - 1 = (f - 1).restrict hsub := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rfl
  have hu' : ((F - 1) ^ m) x' = 0 := by
    apply Subtype.ext
    rw [hrestrict, Module.End.pow_restrict]
    change ((f - 1) ^ m) x = 0
    exact hu
  have hmem : x' ∈ F.genEigenspace 1 m := by
    rw [Module.End.mem_genEigenspace_nat]
    simpa using hu'
  have hfixed : F x' = x' := by
    have h := Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hmem (Commute.refl F) (Langlands.BlockSumParameter.isSemisimple_of_pow_eq_one hn hF).isFinitelySemisimple
      (by simp : IsNilpotent (F - F))
    simpa using h
  exact congrArg Subtype.val hfixed

end Langlands.GroupScheme.Unipotent
