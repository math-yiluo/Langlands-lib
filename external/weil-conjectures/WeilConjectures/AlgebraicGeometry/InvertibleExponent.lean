/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Coefficient rings whose exponent is invertible on a scheme

Torsion étale cohomology behaves well only when the order of the coefficients is invertible
on the base: in characteristic `p` the Artin–Schreier sequence makes `H¹(𝔸¹_k, ℤ/p)` infinite
dimensional, so neither acyclicity of the affine line, nor constructibility of higher direct
images, nor purity survives. This file records that hypothesis as a class.

## Main definitions

- `AlgebraicGeometry.HasInvertibleExponent`: some positive integer annihilating the
  coefficient ring is invertible on the scheme.

## Main statements

- `AlgebraicGeometry.HasInvertibleExponent.of_hom`: the hypothesis passes to `Y`-schemes.
- `AlgebraicGeometry.HasInvertibleExponent.of_hom_of_nonempty`: it descends from a nonempty
  scheme over a field to the field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The coefficient ring `Λ` *has invertible exponent on `X`* if some positive integer `n` with
`n • Λ = 0` becomes a unit in `Γ(X, ⊤)`. For `Λ = A_{E,n}` this is the standing hypothesis
`ℓ` invertible on `X` of the purity chapter; it is exactly what rules out the
Artin–Schreier counterexamples in characteristic `p`. -/
class HasInvertibleExponent (Λ : Type*) [CommRing Λ] (X : Scheme.{u}) : Prop where
  /-- Some positive integer annihilating `Λ` is a unit in `Γ(X, ⊤)`. -/
  exists_isUnit_natCast : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0 ∧ IsUnit (n : Γ(X, ⊤))

/-- If the exponent of `Λ` is invertible on `Y`, it is invertible on every `Y`-scheme. -/
theorem HasInvertibleExponent.of_hom {Λ : Type*} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasInvertibleExponent Λ Y] : HasInvertibleExponent Λ X := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  exact ⟨n, hn, hΛ, by simpa using hu.map f.appTop.hom⟩

/-- If the exponent of `Λ` is invertible on a nonempty scheme `X` over a field `k`, it is
invertible on `k`: otherwise it would vanish in `k`, hence in `Γ(X, ⊤)`, which is nonzero. -/
theorem HasInvertibleExponent.of_hom_of_nonempty {Λ : Type*} [CommRing Λ] {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [HasInvertibleExponent Λ X] [Nonempty X] :
    HasInvertibleExponent Λ (Spec (.of k)) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  refine ⟨n, hn, hΛ, ?_⟩
  have hk : (n : k) ≠ 0 := by
    intro h0
    have : (n : Γ(X, ⊤)) = 0 := by
      rw [← map_natCast aX.appTop.hom, ← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom, h0,
        map_zero, map_zero]
    rw [this] at hu
    obtain ⟨x⟩ := ‹Nonempty X›
    exact not_isUnit_zero (M₀ := X.presheaf.stalk x)
      (by simpa using hu.map (X.presheaf.germ ⊤ x trivial).hom)
  simpa using (Ne.isUnit hk).map (Scheme.ΓSpecIso (.of k)).inv.hom

end AlgebraicGeometry
