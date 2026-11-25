/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Naturality of `Spec.mapMulEquiv`

Precomposing the morphism of affine schemes `Spec T ⟶ Spec S` given by an algebra homomorphism
`S → T` with `Spec U ⟶ Spec T`, for an algebra homomorphism `T → U`, corresponds to composing the
algebra homomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory WithConv

namespace AlgebraicGeometry

variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U] [Bialgebra R S]
  [Algebra R T] [Algebra R U]

/-- The square
```
Spec U ──Spec φ──▶ Spec T
     ╲                │
      ╲               │ Spec ψ
       ╲              ▼
        ╲──Spec (φ ∘ ψ)──▶ Spec S
```
over `Spec R` commutes. -/
theorem Spec.map_asOver_comp_mapMulEquiv (φ : T →ₐ[R] U) (ψ : WithConv (S →ₐ[R] T)) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of R)) ≫ Spec.mapMulEquiv ψ =
      Spec.mapMulEquiv (toConv (φ.comp ψ.ofConv)) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end AlgebraicGeometry
