/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi

/-!
# A basis for the kernel of a functional with a unit basis value

Source: Stacks Project, Algebra, Tag 00MT, the changes of basis and complementary spans.
(blueprint: lem-weil-pbc-kernel-basis-unit-value).
-/

@[expose] public section

universe u v

namespace Module.Basis

/-- Removing a unit pivot from a functional gives a finite free kernel.
Source: Stacks Project, Algebra, Tag 00MT, proof, changes of basis and complementary spans.
(blueprint: lem-weil-pbc-kernel-basis-unit-value).

Proof: Restrict the coordinate map of `b` to the kernel, retaining only the coordinates
indexed by `{k : Fin n // k ≠ p}`. This map is injective: a kernel vector whose remaining
coordinates vanish is `r • b p`, and applying `ℓ` gives `r * ℓ (b p) = 0`. Since the second
factor is a unit, `r = 0`. It is surjective: extend the prescribed remaining coordinates
by zero at `p`, use `b.equivFun.symm` to obtain a vector `v`, and replace `v` by
`v - (a⁻¹ * ℓ v) • b p`, where `a = ℓ (b p)` and `a⁻¹` is the inverse unit. The new vector
lies in the kernel and has exactly the prescribed remaining coordinates. Thus the
coordinate map is a linear equivalence. Its inverse gives a basis of the kernel, and
`finSuccAboveEquiv` reindexes it by `Fin (n - 1)`. This is the coordinate form of the
source's subtraction of the pivot component and its complementary span. The argument
also works in the zero ring; `p : Fin n` rules out `n = 0`. -/
theorem exists_basis_ker_of_isUnit_value
    {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    {n : ℕ} (b : Module.Basis (Fin n) R F) (ℓ : F →ₗ[R] R) (p : Fin n)
    (hunit : IsUnit (ℓ (b p))) :
    Nonempty (Module.Basis (Fin (n - 1)) R (LinearMap.ker ℓ)) := by
  classical
  cases n with
  | zero => exact Fin.elim0 p
  | succ m =>
    obtain ⟨u, hu⟩ := hunit
    let I := {k : Fin (m + 1) // k ≠ p}
    let L : LinearMap.ker ℓ →ₗ[R] (I → R) :=
      LinearMap.pi fun k => (b.coord k.val).comp (LinearMap.ker ℓ).subtype
    have hinj : Function.Injective L := by
      apply (injective_iff_map_eq_zero L).mpr
      intro x hx
      have hrepr : b.repr (x : F) = Finsupp.single p (b.repr (x : F) p) := by
        ext k
        by_cases hk : k = p
        · subst k; simp
        · have hh := congrFun hx (⟨k, hk⟩ : I)
          simpa [L, Module.Basis.coord_apply, Finsupp.single_apply, hk, Ne.symm hk] using hh
      have hvec : (x : F) = b.repr (x : F) p • b p := by
        apply b.repr.injective
        rw [hrepr]
        simp
      have hval : b.repr (x : F) p * (↑u : R) = 0 := by
        have hh := x.property
        change ℓ (x : F) = 0 at hh
        rw [hvec, map_smul, ← hu] at hh
        exact hh
      have hc : b.repr (x : F) p = 0 := by
        have hh := congrArg (fun t : R => t * (↑(u⁻¹) : R)) hval
        simpa [mul_assoc] using hh
      apply Subtype.ext
      simpa [hc] using hvec
    have hsurj : Function.Surjective L := by
      intro c
      let y : Fin (m + 1) → R := fun k => if h : k = p then 0 else c ⟨k, h⟩
      let v : F := b.equivFun.symm y
      let x : F := v - ((↑(u⁻¹) : R) * ℓ v) • b p
      have hx : x ∈ LinearMap.ker ℓ := by
        change ℓ x = 0
        simp [x, map_smul, ← hu, smul_eq_mul, mul_comm]
      refine ⟨⟨x, hx⟩, ?_⟩
      ext k
      change b.coord k.val x = c k
      change b.coord k.val (v - ((↑(u⁻¹) : R) * ℓ v) • b p) = c k
      rw [map_sub, map_smul]
      have hv : b.coord k.val v = y k.val := b.coord_equivFun_symm k.val y
      rw [hv]
      simp [y, k.property, Module.Basis.coord_apply]
    let e : LinearMap.ker ℓ ≃ₗ[R] (I → R) := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
    let bI := Module.Basis.ofEquivFun e
    exact ⟨bI.reindex (finSuccAboveEquiv p).symm⟩

end Module.Basis
