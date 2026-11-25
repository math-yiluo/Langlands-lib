/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.SheafDgHomotopySystem

/-! The homotopy-system and localization steps produce a standard derived
structure for each coefficient algebra.

Source: Stacks sdga, Tags 0FS7, 0FT4 and 0FT5
(blueprint: lem-sfb-ringed-dg-derived-structures).

Proof in words: construct signed shifts and cone triangles on the dg-module
homotopy category, then transport the cone characterization through the
localization universal property.  The construction is performed separately
for each algebra, so this is one component of the scalar-adjunction proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Localize the supplied homotopy system and transport its standard shift and
cone characterization to the fixed localization of actual modules.
Source: Stacks sdga, 0FT5 and derived, 05R6
(blueprint: lem-sfb-ringed-dg-derived-structures).

Proof: the composite from modules to the localization of the homotopy category
is a localization at underlying quasi-isomorphisms: the cylinder argument makes
homotopic maps equal in every such localization.  Use its universal property to
identify it with the fixed localization.  Transfer the localized triangulation,
shift comparisons and cone characterization through this equivalence.  Shift
naturality and the distinguished-triangle criterion follow by applying the
localization functor to the corresponding fields of the supplied homotopy system.
-/
theorem derived_structure_from_homotopy_system
    (O : Sheaf J CommRingCat.{u}) (A : Algebra.{c, v, u} O) (hs : HomotopySystem A) :
    Nonempty (DerivedStructure A) := by
  sorry

end CategoryTheory.RingedSiteDg
