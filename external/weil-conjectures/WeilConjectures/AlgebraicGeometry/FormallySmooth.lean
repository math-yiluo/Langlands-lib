/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Over

/-!
# Formally smooth morphisms of schemes

Source: Stacks Project, More on Morphisms, Definition 37.11.1 (Tag 02H0)
(blueprint: def-sbc-formally-smooth).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: def-sbc-formally-smooth) A morphism `f : X ⟶ S` is formally smooth
if every `S`-morphism from an affine first order thickening's closed subscheme
to `X` extends over the affine thickening. The structure map of `T` is the
composite `i ≫ (T' ↘ S)` (Stacks Project, Tag 02H0). -/
def FormallySmooth {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ {T T' : Scheme.{u}} (i : T ⟶ T') [IsAffine T] [IsAffine T'] [T'.Over S],
    IsFirstOrderThickening i →
      ∀ (a : T ⟶ X), a ≫ f = i ≫ (T' ↘ S) →
        ∃ a' : T' ⟶ X, i ≫ a' = a ∧ a' ≫ f = T' ↘ S

end AlgebraicGeometry
