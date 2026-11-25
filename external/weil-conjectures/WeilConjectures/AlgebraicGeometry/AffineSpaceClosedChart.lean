/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Affine schemes of finite type are closed in affine space

An affine scheme `U` locally of finite type over an affine scheme `V` is a closed subscheme of
some affine space `𝔸ⁿ_V`: choose finitely many generators of `Γ(U)` as a `Γ(V)`-algebra.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine scheme locally of finite type over an affine scheme `V` admits a closed immersion
into a relative affine space `𝔸ⁿ_V` over `V`. -/
theorem exists_isClosedImmersion_affineSpace_of_isAffine {U V : Scheme.{u}} [IsAffine U]
    [IsAffine V] (g : U ⟶ V) [LocallyOfFiniteType g] :
    ∃ (n : ℕ) (c : U ⟶ 𝔸(ULift.{u} (Fin n); V)),
      c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V = g ∧ IsClosedImmersion c := by
  have hft : g.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType g ‹_›
  let := g.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  let v : ULift.{u} (Fin s.card) → Γ(U, ⊤) := fun i ↦ (s.equivFin.symm i.down : Γ(U, ⊤))
  refine ⟨s.card, AffineSpace.homOfVector g v, AffineSpace.homOfVector_over _ _,
    AffineSpace.isClosedImmersion_homOfVector g v ?_⟩
  have hrange : Set.range v = (s : Set Γ(U, ⊤)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i.down).2
    · intro hx
      exact ⟨⟨s.equivFin ⟨x, hx⟩⟩, by simp [v]⟩
  rw [hrange]
  have := Algebra.adjoin_eq_ring_closure (R := Γ(V, ⊤)) (A := Γ(U, ⊤)) (s : Set Γ(U, ⊤))
  rw [hs] at this
  exact this.symm.trans Algebra.top_toSubring

end AlgebraicGeometry
