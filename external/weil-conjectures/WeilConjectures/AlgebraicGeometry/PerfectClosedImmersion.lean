/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Perfect closed immersions

Source: Stacks Project, More on Morphisms, Tag 0687, Definition 37.61.2,
and More on Algebra, Tag 068Y, Lemma 15.84.2 (blueprint: def-sc-perfect-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
(blueprint: def-sc-perfect-closed-immersion)

A closed immersion is perfect when it is affine-locally the quotient immersion
for an ideal whose quotient module has a bounded resolution by finite projective
modules. The equation identifies the restricted morphism with the quotient map,
not just its source scheme with the quotient spectrum.
-/
def IsPerfectClosedImmersion {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] : Prop :=
  ∀ x : Y, ∃ (U : Y.Opens), x ∈ U ∧ IsAffineOpen U ∧
    ∃ (I : Ideal (Γ(Y, U))),
      (∃ e : Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅
          AlgebraicGeometry.Spec (CommRingCat.of ((Γ(Y, U) : Type u) ⧸ I)),
        i ∣_ U ≫ U.toSpecΓ =
          e.hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ∧
      ∃ (P : CategoryTheory.ProjectiveResolution
          (ModuleCat.of (Γ(Y, U) : Type u) ((Γ(Y, U) : Type u) ⧸ I))),
        (∀ n, Module.Finite (Γ(Y, U) : Type u) (P.complex.X n)) ∧
          (∀ n, Module.Projective (Γ(Y, U) : Type u) (P.complex.X n)) ∧
            ∃ N : ℕ, ∀ n, N ≤ n → IsZero (P.complex.X n)

end AlgebraicGeometry
