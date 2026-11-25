/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedSiteDgModules

/-! Derived restriction descends from the literal dg restriction and is exact.

Source: the restriction part of Stacks sdga, Tags 0FT4 and 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact).

Proof in words: restriction keeps the underlying complex, hence preserves
quasi-isomorphisms, shifts and mapping-cone triangles.  The localization
universal property supplies the functor and its factorization isomorphism;
the cone characterization then supplies exactness.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The exact localization lift of literal restriction, with its fixed comparison. -/
structure RestrictionDescentData {O : Sheaf J CommRingCat.{u}}
    {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] where
  restriction : Derived B ⥤ Derived A
  restrictionIso : Q B ⋙ restriction ≅ RingedSiteDg.restriction φ ⋙ Q A
  [restrictionShift : restriction.CommShift ℤ]
  restrictionExact : restriction.IsTriangulated

/-- Restriction retains the whole underlying complex, so it preserves quasi-isomorphisms.
Source: Stacks sdga, 0FT4
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
theorem restriction_preserves_quasiisomorphisms
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    {M N : Module B} (f : M ⟶ N) (hf : quasiIsomorphisms B f) :
    quasiIsomorphisms A ((RingedSiteDg.restriction φ).map f) := by
  exact hf

/-- The literal descended restriction, constructed by localization.
Source: Stacks sdga, 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
def derivedRestriction
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B) :
    Derived B ⥤ Derived A :=
  Localization.lift (RingedSiteDg.restriction φ ⋙ Q A)
    (fun _ _ f hf ↦ Localization.inverts (Q A) (quasiIsomorphisms A) _
      (restriction_preserves_quasiisomorphisms φ f hf)) (Q B)

/-- The fixed factorization of the literal descended restriction.
Source: Stacks sdga, 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
def derivedRestrictionIso
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B) :
    Q B ⋙ derivedRestriction φ ≅ RingedSiteDg.restriction φ ⋙ Q A :=
  Localization.fac (RingedSiteDg.restriction φ ⋙ Q A)
    (fun _ _ f hf ↦ Localization.inverts (Q A) (quasiIsomorphisms A) _
      (restriction_preserves_quasiisomorphisms φ f hf)) (Q B)

/-- The descended literal restriction respects standard shifts and cone triangles.
Source: Stacks sdga, 0FT5 and derived, 05R6
(blueprint: lem-sfb-ringed-dg-restriction-localization-exact).

Proof: restriction leaves the underlying complexes and the cone matrices
unchanged and changes actions only by precomposition with the algebra map.
It therefore carries a specified shift or cone comparison to the corresponding
comparison over A.  Use the shift naturality fields to descend these comparisons
and the localized-cone characterization of distinguished triangles to prove
exactness of the constructed localization lift.
-/
theorem restriction_localization_exact
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] :
    ∃ (_ : (derivedRestriction φ).CommShift ℤ),
      (derivedRestriction φ).IsTriangulated := by
  sorry

/-- Package the constructed localization lift with its shift and exactness data.
Source: Stacks sdga, 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
theorem restriction_descends_and_is_exact
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] :
    Nonempty (RestrictionDescentData φ) := by
  obtain ⟨hshift, hexact⟩ := restriction_localization_exact φ
  exact ⟨{
    restriction := derivedRestriction φ
    restrictionIso := derivedRestrictionIso φ
    restrictionShift := hshift
    restrictionExact := hexact
  }⟩

end CategoryTheory.RingedSiteDg
