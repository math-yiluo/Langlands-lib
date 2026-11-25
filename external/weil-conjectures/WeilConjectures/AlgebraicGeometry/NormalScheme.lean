/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normal schemes, Galois covers and deck groups

Source: the smooth base change blueprint, node `def-sbc-normal-dominant-galois`, order 1379
(blueprint: def-sbc-normal-dominant-galois).

The other notions in this node already exist as `AlgebraicGeometry.IsIntegral`,
`AlgebraicGeometry.IsDominant`, `AlgebraicGeometry.GeometricallyConnected`, and
`AlgebraicGeometry.GeometricallyReduced`. The existing `Scheme.GaloisCover` requires a finite
group, so `Scheme.GaloisCoverAction` covers the unrestricted group in the source.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral scheme is normal when every local ring is an integrally closed domain.
Source: smooth base change blueprint, node `def-sbc-normal-dominant-galois`, order 1379
(blueprint: def-sbc-normal-dominant-galois). -/
def IsNormalScheme (S : Scheme.{u}) : Prop :=
  IsIntegral S ∧ ∀ s : S,
    IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)

/-- A finite etale Galois cover with an action of an arbitrary group. The action is
simply transitive on each geometric fibre; `quotient` expresses the scheme quotient.
Unlike `Scheme.GaloisCover`, this permits infinite groups over the empty base. On a
nonempty base simple transitivity and finiteness of the morphism force the group to be finite.
The group laws make each action map an automorphism, hence a finite etale morphism.
Source: smooth base change blueprint, node `def-sbc-normal-dominant-galois`, order 1379
(blueprint: def-sbc-normal-dominant-galois). -/
structure Scheme.GaloisCoverAction (G : Type v) [Group G] (C : Scheme.{u}) where
  /-- The total space. -/
  Z : Scheme.{u}
  /-- The structure morphism. -/
  π : Z ⟶ C
  /-- The structure morphism is finite. -/
  [isFinite : IsFinite π]
  /-- The structure morphism is etale. -/
  [etale : Etale π]
  /-- A torsor covers the base. -/
  [surjective : Surjective π]
  /-- The action maps. -/
  smul : G → (Z ⟶ Z)
  /-- The action is over the base. -/
  smul_π (g : G) : smul g ≫ π = π
  /-- The identity acts trivially. -/
  one_smul : smul 1 = 𝟙 Z
  /-- The left action law, with categorical composition order. -/
  mul_smul (g h : G) : smul (g * h) = smul h ≫ smul g
  /-- Simple transitivity on geometric fibres, expressed using field-valued lifts. -/
  simply_transitive : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x y : Spec (.of Ω) ⟶ Z), x ≫ π = y ≫ π → ∃! g : G, x ≫ smul g = y
  /-- The quotient universal property in schemes. -/
  quotient : ∀ (W : Scheme.{u}) (f : Z ⟶ W),
    (∀ g : G, smul g ≫ f = f) → ∃! q : C ⟶ W, π ≫ q = f

/-- The deck group is the group of all automorphisms over the base, without requiring
compatibility with a chosen action, with the group structure of `Aut`. This applies also to
covers with an infinite group and empty base.
Source: smooth base change blueprint, node `def-sbc-normal-dominant-galois`, order 1379
(blueprint: def-sbc-normal-dominant-galois). -/
abbrev Scheme.Hom.deckGroup {Z C : Scheme.{u}} (π : Z ⟶ C) : Type _ :=
  Aut (Over.mk π)

end AlgebraicGeometry
