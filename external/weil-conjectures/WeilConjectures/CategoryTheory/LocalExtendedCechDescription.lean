/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedIdealGenerators

/-!
# The augmented local extended Cech description

Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

/-- An augmented complex has the local extended Cech description when each finite
slice-generating list gives a derived isomorphism from its actual extended localization
complex, and the isomorphism commutes with the given augmentations.
Source: Stacks Project, algebraization.tex, Tag 099E
(auxiliary; not a blueprint node). -/
def HasLocalExtendedCechDescription
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O) : Prop :=
  ∀ (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)),
    IsRingedIdealGeneratingList O I ι U r f →
      ∃ e : DerivedCategory.Q.obj
          (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (f i))).1 ≅
            (ringedDerivedRestriction O U).obj (DerivedCategory.Q.obj K),
        e.hom ≫ (ringedDerivedRestriction O U).map (DerivedCategory.Q.map ε) ≫
            (ringedDerivedRingRestrictionIso O U).hom =
          DerivedCategory.Q.map
            (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (f i))).2

end CategoryTheory
