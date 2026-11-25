/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.SixFunctors.SignedDerivedInternalHomExact

/-! Independent-universe exactness interface for derived internal Hom.

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated); blueprint
lem-weil-pbc-ringed-internal-hom-exact-restriction.
-/

@[expose] public section
set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C]

/-- Internal derived Hom is exact in both variables at independent universes.

Source: Stacks Project, Tag 08JC; blueprint
lem-weil-pbc-ringed-internal-hom-exact-restriction.

Proof: For the covariant variable, represent a distinguished triangle by a cone
of K-injective complexes. The cone remains K-injective, and Hom into it is the
cone of the induced Hom map with the normalized target shift. For the
contravariant variable, reverse the cone triangle and use the signed source shift.
The finite biproduct calculations descend through localization and TR3 transfers
the result to arbitrary distinguished triangles. The argument uses only finite
splittings, so the site object, morphism, coefficient, and derived universes are
independent and no boundedness or finite-generation assumption is needed.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-universes) -/
theorem ringedInternalHom_exact
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] :
    (∀ M : D.{c, v, r, w} J R,
      ∃ _ : ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj M).CommShift ℤ,
        ((Functor.curry.obj
          (derivedInternalHomOfUniverses.{c, v, r, w} J R)).flip.obj M).IsTriangulated) ∧
    (∀ K : D.{c, v, r, w} J R,
      ∃ _ : ((Functor.curry.obj
        (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op K)).CommShift ℤ,
        ((Functor.curry.obj
          (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op K)).IsTriangulated) := by
  constructor
  · intro M
    obtain ⟨S, hS, _⟩ := signedDerivedInternalHom_exact.{c, v, r, w} J R M
    exact ⟨S, hS⟩
  · intro K
    exact ⟨homCommShift.{c, v, r, w} J R K,
      hom_isTriangulated.{c, v, r, w} J R K⟩

end CategoryTheory.RingedHomUniverses
