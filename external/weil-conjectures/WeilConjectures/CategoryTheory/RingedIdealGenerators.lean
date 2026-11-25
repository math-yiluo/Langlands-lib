/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Local finite generation of an ideal sheaf on a ringed site

Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node).

An ideal subsheaf is represented by a monomorphism of module sheaves into the rank-one
module sheaf. Specified lists are matched to Mathlib's `GeneratingSections`. Local finite generation
itself is the existing class `SheafOfModules.IsFiniteType`, without a second definition.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- A specified finite list generates an ideal subsheaf when it is the image of Mathlib's
generating sections of that subsheaf on the slice.
Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node).
The generating sections are indexed by a type equivalent to `Fin r`, and their images at
the terminal slice object are the prescribed ring sections. -/
def IsRingedIdealGeneratingList
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) : Prop :=
  ∃ σ : (I.over U).GeneratingSections, ∃ e : σ.I ≃ Fin r,
    ∀ i : σ.I,
      (SheafOfModules.sectionsMap (ι.over U) (σ.s i)).val (op (Over.mk (𝟙 U))) = f (e i)

end CategoryTheory
