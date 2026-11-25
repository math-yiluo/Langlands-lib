/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # The algebra of equivariant functions on the split components

## References

* Stacks Project, Tag 03SF, finite group actions on split covers
-/

@[expose] public section
universe u
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- Equivariant functions, realized as an intersection of algebra equalizers.
The condition is `ρ a (f i) = f (α a i)`; thus no choice of orbit data enters this algebra. -/
def affineTorsorEquivariantAlgebra
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) : Subalgebra H (Fin d → C) :=
  ⨅ a : G, ⨅ i : Fin d,
    AlgHom.equalizer ((ρ a).comp (Pi.evalAlgHom H (fun _ : Fin d ↦ C) i))
      (Pi.evalAlgHom H (fun _ : Fin d ↦ C) (α a i))

end AlgebraicGeometry.Scheme
