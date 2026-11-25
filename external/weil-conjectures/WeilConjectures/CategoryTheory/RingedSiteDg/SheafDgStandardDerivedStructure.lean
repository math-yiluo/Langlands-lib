/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.FiniteFreeDgCoinductionData

/-! Standard triangulation on the fixed sheaf DG-module localization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- The fixed localization of right DG modules has its standard triangulation.

Source: Stacks `sdga.tex`, Tags 0FS7, 0FT2, 0FT4 and 0FT5.

Proof: Take the homotopy system for A. Its W is exactly the morphisms inducing
isomorphisms on all underlying cohomology sheaves, by cohomology_factors and
W_iff_cohomology. Its saturation supplies the fraction calculi and compatibility
with triangles. Localize K(A) at W and apply triangulated localization.

Identify this with the fixed localization of modules as follows. Any functor out
of modules inverting quasi-isomorphisms identifies right-linear homotopic maps:
form the module cylinder using the degreewise sum and shifted summand, with the
usual signed differential and componentwise action. The cylinder projection is a
quasi-isomorphism; its two sections have equal images after inverting it. The
map supplied by a right-linear homotopy then identifies the two original maps.
Thus such a functor factors through the homotopy quotient. Conversely a functor
from K(A) inverting W inverts every module quasi-isomorphism after the quotient.
These two universal properties give mutually inverse equivalences between the
two localizations and identify their functors from modules.

Transport the additive, zero, shift and triangulated structures to Derived A
along this equivalence. Use the homotopy system's actual module shifts and cones
for shifts_exist and cones_exist. Apply the triangulated localization functor to
its shiftIso; the functor's shift comparison and the equivalence give shiftIso
in Derived A. Its naturality follows by applying the two functors to
HomotopyStructure.shift_natural. Every distinguished triangle in a triangulated
localization is isomorphic to an image of a distinguished triangle in K(A), hence
to an image of one of the supplied actual module cones. Conversely every such
image is distinguished, since both functors are triangulated. This proves the
required distinguished_iff, not just one implication. No boundedness of A or
of modules is used; zero modules and zero cones are included.

(blueprint: lem-sfb-sheaf-dg-standard-derived-structure-stage3) -/
theorem sheaf_dg_standard_derived_structure (A : Algebra O) :
    Nonempty (DerivedStructure A) := by sorry

end CategoryTheory.RingedSiteDg
