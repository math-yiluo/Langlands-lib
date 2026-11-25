/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.CategoryTheory.SiteFilteredColimitSections
import Mathlib.CategoryTheory.Filtered.Final

/-! # Sections of the colimit sheaf on a colimit of sites
Source: Stacks Project, Sites, Lemma 09YN and Modules on Sites, Lemma 03CO
(blueprint: lem-weil-pbc-colimit-of-sites-sections).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Lemma 09YN (blueprint: lem-weil-pbc-colimit-of-sites-sections).
The sections of the colimit of inverse-image sheaves are the filtered colimit of the
sections at the corresponding stage objects. The proof applies the finite-covering
section theorem to the diagram `D`.
-/
theorem colimitSite_sections_bijective
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Cat.{u, u}} (V : Cocone F)
    {Q : Precoverage V.pt}
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    [Q.HasPullbacks] (hfinite : Q ≤ Precoverage.finite V.pt)
    (i : J) (U : F.obj i)
    (D : Under i ⥤ Sheaf Q.toGrothendieck (Type u))
    (c : Cocone D) (hc : IsColimit c) :
    Function.Bijective
      (colimit.desc
        (D ⋙ (sheafSections Q.toGrothendieck (Type u)).obj
          (op ((V.ι.app i).toFunctor.obj U)))
        (((sheafSections Q.toGrothendieck (Type u)).obj
          (op ((V.ι.app i).toFunctor.obj U))).mapCocone c)) := by
  exact siteFilteredColimit_sections_bijective Q hfinite D c hc
    ((V.ι.app i).toFunctor.obj U)

/-- Source: Stacks Project, Modules on Sites, Lemma 03CO
(blueprint: lem-weil-pbc-colimit-of-sites-sections).
The same assertion for abelian sheaves says that the canonical map of section groups is
an isomorphism, by the abelian finite-covering section theorem.
-/
theorem colimitSite_sections_isIso
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Cat.{u, u}} (V : Cocone F)
    {Q : Precoverage V.pt}
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    [Q.HasPullbacks] (hfinite : Q ≤ Precoverage.finite V.pt)
    (i : J) (U : F.obj i)
    (D : Under i ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone D) (hc : IsColimit c) :
    IsIso
      (colimit.desc
        (D ⋙ (sheafSections Q.toGrothendieck AddCommGrpCat.{u}).obj
          (op ((V.ι.app i).toFunctor.obj U)))
        (((sheafSections Q.toGrothendieck AddCommGrpCat.{u}).obj
          (op ((V.ι.app i).toFunctor.obj U))).mapCocone c)) := by
  exact siteFilteredColimit_sections_isIso Q hfinite D c hc
    ((V.ι.app i).toFunctor.obj U)

end CategoryTheory
