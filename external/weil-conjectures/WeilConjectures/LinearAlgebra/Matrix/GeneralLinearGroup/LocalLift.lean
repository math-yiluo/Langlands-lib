/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Lifting invertible matrices along surjective local homomorphisms

If `f : R →+* S` is a surjective local ring homomorphism, then
`Matrix.GeneralLinearGroup.map f : GL n R → GL n S` is surjective: any lift of an invertible
matrix has a determinant mapping to a unit, hence is itself invertible. In particular this
applies to any surjection out of a local ring, e.g. `𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ`; it is used to
make the transition maps of a tower of free modules standard.

- `Matrix.GeneralLinearGroup.map_surjective_of_isLocalHom`
- `Matrix.GeneralLinearGroup.map_surjective_of_isLocalRing`
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S]

/-- **Lifting invertible matrices along a surjective local homomorphism**: if `f : R →+* S` is
surjective and local (an element of `R` is a unit as soon as its image is), every invertible
matrix over `S` lifts to an invertible matrix over `R`: lift the entries; the determinant of the
lift maps to a unit, hence is a unit. -/
theorem map_surjective_of_isLocalHom (f : R →+* S) [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Surjective (map (n := n) f) := by
  intro A
  let B : Matrix n n R := (A : Matrix n n S).map (Function.surjInv hf)
  have hB : B.map f = A := by
    ext i j
    exact Function.surjInv_eq hf _
  have hdet : IsUnit B.det := by
    refine isUnit_of_map_unit f _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hB]
    exact (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  refine ⟨nonsingInvUnit B hdet, Units.ext ?_⟩
  exact hB

/-- Over a local ring, every invertible matrix over a nonzero quotient lifts: `GL_r(R) → GL_r(S)`
is surjective for a surjection `R → S` from a local ring onto a nontrivial ring, e.g.
`𝒪_E ⧸ ℓⁿ⁺¹ → 𝒪_E ⧸ ℓⁿ`. -/
theorem map_surjective_of_isLocalRing [IsLocalRing R] [Nontrivial S] (f : R →+* S)
    (hf : Function.Surjective f) : Function.Surjective (map (n := n) f) :=
  have := IsLocalHom.of_surjective f hf
  map_surjective_of_isLocalHom f hf

end Matrix.GeneralLinearGroup
