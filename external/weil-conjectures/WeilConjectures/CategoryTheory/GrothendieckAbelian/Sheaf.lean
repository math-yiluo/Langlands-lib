/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The sheaf categories on essentially small sites are Grothendieck abelian

The category of `A`-valued sheaves on an essentially small site is Grothendieck abelian,
for a Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes: the site is equivalent to a small one, so the sheaf
category is equivalent to a category of sheaves on a small site, which is Grothendieck
abelian. Since the site has `Hom`-types in `u`, the sheaf category again has `Hom`-types in
`u + 1`.

The small étale site and the small pro-étale site are essentially small in `u + 1`, so this
applies to both.

The small `Q`-sites of `P`-schemes and their localizations are essentially small too, and
the instances for them are recorded here as well.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on an essentially small site is Grothendieck
abelian, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u + 1`, one above the universe `u` of the base schemes: the site is equivalent to
a small one, and sheafification is available on both by `hasSheafify_of_essentiallySmall`. -/
instance (priority := high) isGrothendieckAbelian_sheaf_of_essentiallySmall (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes over a scheme
`U` is Grothendieck abelian: the site is essentially `u + 1`-small, so this is a case of
the instance above. -/
instance isGrothendieckAbelian_sheaf_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify A _

/-- The category of `A`-valued sheaves on the small étale site is Grothendieck abelian:
the instance above applied to the essentially small small étale site. For `A = Ab` the abelian
sheaves on the small étale site form an abelian category (`CategoryTheory.sheafIsAbelian`) with
all small colimits. (blueprint: `situation-conventions`) -/
instance (priority := high) isGrothendieckAbelian_sheaf_smallEtaleTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology A) :=
  inferInstance

/-- The category of `A`-valued sheaves on the small pro-étale site is Grothendieck abelian:
the instance above applied to the essentially small small pro-étale site. -/
instance (priority := high) isGrothendieckAbelian_sheaf_proEtTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (Scheme.ProEt.topology X) A) :=
  inferInstance

/-- The category of `A`-valued sheaves on the localization at `V` of the small `Q`-site of
`P`-schemes over `U` is Grothendieck abelian: the slice of the site at `V` is again
essentially `u + 1`-small. -/
instance isGrothendieckAbelian_sheaf_over_smallGrothendieckTopology (A : Type u')
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) (V : P.Over ⊤ U) :
    IsGrothendieckAbelian.{u + 1} (Sheaf ((U.smallGrothendieckTopology Q (Q := P)).over V) A) :=
  Sheaf.isGrothendieckAbelian_of_hasSmallSiteSheafify A _

end CategoryTheory.GrothendieckTopology
