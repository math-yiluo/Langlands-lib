/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.unusedVariables false
namespace AlgebraicGeometry.Scheme
/-- If the subgroups `K k` of `G` agree, up to a reindexing `Fin m ≃ Fin D.m`, with the
stabilizers of the fixed orbit data `D`, then the products of the fixed subalgebras `C^{K k}`
and `C^{D.stabilizer k}` are isomorphic as `H`-algebras. -/
theorem fixed_orbit_product_equiv
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) (D : FixedOrbitData G d)
    (hD : D.action = α) :
    ∀ (m : ℕ) (K : Fin m → Subgroup G),
      (∃ e : Fin m ≃ Fin D.m, ∀ k, K k = D.stabilizer (e k)) →
      Nonempty ((∀ k : Fin m,
        (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)) ≃ₐ[H]
      (∀ k : Fin D.m,
        (⨅ ζ : D.stabilizer k,
          AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C))) := by
  intro m K hcompat
  obtain ⟨e, hK⟩ := hcompat
  have hfamily : K = fun k ↦ D.stabilizer (e k) := funext hK
  subst K
  exact ⟨AlgEquiv.piCongrLeft H
    (fun k : Fin D.m ↦
      (⨅ ζ : D.stabilizer k,
        AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)) e⟩


end AlgebraicGeometry.Scheme
