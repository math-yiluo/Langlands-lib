/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-! # Perfect ring complexes with an arbitrary localization universe

Source: blueprint def-pc-perfect-ring-complex, bounded finite projective definition
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace DerivedCategory

/-- Perfectness means a bounded complex of finitely generated projective modules,
without identifying the localization universe with the coefficient universe.
Source: blueprint def-pc-perfect-ring-complex
(auxiliary; not a blueprint node). -/
def IsPerfectRingComplex {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (C : DerivedCategory (ModuleCat.{u} R)) :
    Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    (∀ i : ℤ, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧
    Nonempty (C ≅ Q.obj P)

end DerivedCategory
