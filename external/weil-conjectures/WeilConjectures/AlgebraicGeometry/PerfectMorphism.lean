/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Stalkwise finite Tor dimension of scheme morphisms

Source: Stacks Project, More on Morphisms, Lemma 37.61.11, condition (3), and
Lemma 37.61.13, Tag 0B6G (blueprint: def-pc-perfect-morphism).
-/

@[expose] public section

universe uTor

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

/-- Every source local ring has finite Tor dimension over the target local ring,
with scalar restriction through the actual stalk map. The bound may depend on the point,
but must hold for every test module. For a finite type morphism over a Noetherian base,
this is equivalent to being perfect by Stacks Lemma 37.61.11. It is not the definition
of a perfect morphism without the pseudo-coherence hypothesis of that lemma.
Source: Stacks Project, More on Morphisms, Lemma 37.61.11, condition (3)
(blueprint: def-pc-perfect-morphism). -/
def HasStalkwiseFiniteTorDimension {X Y : Scheme.{uTor}} (f : X ⟶ Y) : Prop :=
  ∀ x : X, ∃ n : ℕ, ∀ M : ModuleCat.{uTor} (Y.presheaf.stalk (f x)),
    ∀ i : ℕ, n < i →
      IsZero (((Tor' (ModuleCat.{uTor} (Y.presheaf.stalk (f x))) i).obj
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj M)

end AlgebraicGeometry
