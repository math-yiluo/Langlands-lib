/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Derived restriction to the slice of a ringed site

Source: Stacks Project, Modules on Sites, Tag 03DJ, and Cohomology on Sites, Tag 08JB
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- The ringed-site derived category, using the recorded module-sheaf and derived-category
notions verbatim.
Source: Stacks Project, Cohomology on Sites, Tag 08JB
(auxiliary; not a blueprint node). -/
abbrev ringedSiteDerived
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] :=
  DerivedCategory (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))

/-- Slice restriction is additive.
Source: Stacks Project, Modules on Sites, Tag 03DJ
(auxiliary; not a blueprint node).
Proof: addition of maps is sectionwise, and slice restriction only precomposes their
components with the forgetful functor from the slice category. -/
theorem ringedOverFunctor_additive (U : C) :
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- Slice restriction preserves finite limits.
Source: Stacks Project, Modules on Sites, Tag 03DJ
(auxiliary; not a blueprint node).
Proof: finite limits of module sheaves are computed sectionwise, so precomposition
with the forgetful functor from the slice commutes with them. -/
theorem ringedOverFunctor_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let F := SheafOfModules.overFunctor.{u} R U
  have e : F ⋙ SheafOfModules.toSheaf (R.over U) ≅
      SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u} U := Iso.refl _
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf (R.over U)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves F
    (SheafOfModules.toSheaf (R.over U))

/-- Slice restriction preserves finite colimits.
Source: Stacks Project, Modules on Sites, Tag 03DJ
(auxiliary; not a blueprint node).
Proof: finite colimits are the sheafifications of sectionwise colimits. Covering sieves
on a slice are exactly those induced from the original site, so sheafification commutes
with slice restriction. Sectionwise colimits commute with precomposition. -/
theorem ringedOverFunctor_preservesFiniteColimits (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let F := SheafOfModules.overFunctor.{u} R U
  let H := J.overPullback AddCommGrpCat.{u} U
  have : PreservesColimitsOfSize.{u, u} H :=
    ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over U) J).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf (R.over U)
  have : PreservesFiniteColimits (F ⋙ T) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves F T

attribute [instance] ringedOverFunctor_additive ringedOverFunctor_preservesFiniteLimits
  ringedOverFunctor_preservesFiniteColimits

/-- Restriction on unbounded derived categories, induced by exact module restriction.
Source: Stacks Project, Cohomology on Sites, Tag 08JB
(auxiliary; not a blueprint node). -/
def ringedDerivedRestriction (U : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [hU : HasDerivedCategory.{w'} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))] :
    ringedSiteDerived O ⥤ ringedSiteDerived (O.over U) :=
  letI : HasDerivedCategory.{w'} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) := hU
  (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapDerivedCategory

/-- Restriction of the rank-one ring module is the rank-one ring module on the slice.
Source: Stacks Project, Modules on Sites, Tag 03DJ
(auxiliary; not a blueprint node). -/
def ringedOverRingIso (U : C) :
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ≅
      SheafOfModules.unit
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)) :=
  Iso.refl _

/-- Restriction of the ring complex is canonically the ring complex on the slice.
Source: Stacks Project, Cohomology on Sites, Tag 08JB
(auxiliary; not a blueprint node). -/
def ringedRestrictionRingComplexIso (U : C) :
    ((SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U) (ComplexShape.up ℤ) 0).app
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) ≪≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso (ringedOverRingIso O U)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison between restriction of the ring in degree zero and the ring
of the slice in degree zero.
Source: Stacks Project, Cohomology on Sites, Tag 08JB
(auxiliary; not a blueprint node). -/
def ringedDerivedRingRestrictionIso (U : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [hU : HasDerivedCategory.{w'} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))] :
    (ringedDerivedRestriction O U).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q).obj
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q).obj
        (SheafOfModules.unit
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))) :=
  letI : HasDerivedCategory.{w'} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) := hU
  let F := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U
  F.mapDerivedCategoryFactors.app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))) ≪≫
    DerivedCategory.Q.mapIso (ringedRestrictionRingComplexIso O U)

end CategoryTheory
