/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies

set_option linter.privateModule false

/-!
# Exactness of geometric inverse image on abelian sheaves and modules

Source: Stacks Project, Modules on Sites, Tags 04JC, 03D2, 03DA and 03DB;
Sites, Proposition 00YV (2)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w uC vC uD vD

open CategoryTheory.Limits

namespace CategoryTheory.GeometricMorphism

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

private noncomputable abbrev abSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} :=
  hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}

private noncomputable abbrev smallArrowLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (U : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
      AddCommGrpCat.{w} :=
  HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _

attribute [local instance] abSheafify smallArrowLimits

private noncomputable abbrev abLocallyBijective
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
    (A := AddCommGrpCat.{w})

attribute [local instance] abLocallyBijective

private theorem abForgetLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))

attribute [local instance] abForgetLimits

open CategoryTheory.MonoidalCategory
open SheafOfModules.GeometricConstruction

private def abelianObjects
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{w} ⥤ CommGrp (Sheaf J (Type w)) := by
  let S := sheafCompose J (forget AddCommGrpCat.{w})
  let obj (A : Sheaf J AddCommGrpCat.{w}) : CommGrp (Sheaf J (Type w)) := by
    letI : GrpObj (S.obj A) := {
      one := ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : A.obj.obj U))
                naturality := by intro U V f; ext x; exact (A.obj.map f).hom.map_zero.symm }⟩
      mul := ⟨{ app := fun U ↦ ↾(fun x ↦
                  (show A.obj.obj U from x.1) + (show A.obj.obj U from x.2))
                naturality := by intro U V f; ext x; exact ((A.obj.map f).hom.map_add _ _).symm }⟩
      one_mul := by ext U x; exact zero_add (show A.obj.obj U from x.2)
      mul_one := by ext U x; exact add_zero (show A.obj.obj U from x.1)
      mul_assoc := by ext U x; exact add_assoc (show A.obj.obj U from x.1.1) x.1.2 x.2
      inv := ⟨{ app := fun U ↦ ↾(fun x ↦ -(show A.obj.obj U from x))
                naturality := by intro U V f; ext x; exact ((A.obj.map f).hom.map_neg _).symm }⟩
      left_inv := by ext U x; exact neg_add_cancel (show A.obj.obj U from x)
      right_inv := by ext U x; exact add_neg_cancel (show A.obj.obj U from x) }
    exact { X := S.obj A
            comm := { mul_comm := by ext U x; exact add_comm (show A.obj.obj U from x.2) x.1 } }
  exact {
    obj := obj
    map := fun f ↦ InducedCategory.homMk (Grp.homMk'' (S.map f)
      (by ext U x; exact (f.hom.app U).hom.map_zero)
      (by ext U x; exact (f.hom.app U).hom.map_add _ _)) }

@[instance_reducible] private def ringStructure
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{w}) :
    CommRingObj ((sheafCompose J (forget CommRingCat.{w})).obj A) where
  zero := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : A.obj.obj U))
             naturality := by
               intro X Y f
               ext x
               change (0 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_zero _).symm }⟩
  add := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 + x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 + (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 + x.2)
              exact (map_add _ _ _).symm }⟩
  neg := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U ↦ -x)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X at x
              change -(A.obj.map f).hom x = (A.obj.map f).hom (-x)
              exact (map_neg _ _).symm }⟩
  one := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : A.obj.obj U))
            naturality := by
               intro X Y f
               ext x
               change (1 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_one _).symm }⟩
  mul := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 * x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 * (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 * x.2)
              exact (map_mul _ _ _).symm }⟩
  zero_add := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (0 : A.obj.obj U) + x.2 = x.2
    exact zero_add x.2
  add_zero := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) + 0 = x.1
    exact add_zero x.1
  add_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) + x.1.2 + x.2 = x.1.1 + (x.1.2 + x.2)
    exact add_assoc x.1.1 x.1.2 x.2
  left_neg := by
    ext U x
    change A.obj.obj U at x
    change -(x : A.obj.obj U) + x = 0
    exact neg_add_cancel x
  right_neg := by
    ext U x
    change A.obj.obj U at x
    change (x : A.obj.obj U) + -x = 0
    exact add_neg_cancel x
  add_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) + x.1 = x.1 + x.2
    exact add_comm x.2 x.1
  one_mul := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (1 : A.obj.obj U) * x.2 = x.2
    exact one_mul x.2
  mul_one := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) * 1 = x.1
    exact mul_one x.1
  mul_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) * x.1.2 * x.2 = x.1.1 * (x.1.2 * x.2)
    exact mul_assoc x.1.1 x.1.2 x.2
  mul_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) * x.1 = x.1 * x.2
    exact mul_comm x.2 x.1
  mul_add := by
    ext U x
    change A.obj.obj U × (A.obj.obj U × A.obj.obj U) at x
    change (x.1 : A.obj.obj U) * (x.2.1 + x.2.2) = x.1 * x.2.1 + x.1 * x.2.2
    exact mul_add x.1 x.2.1 x.2.2
  add_mul := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change ((x.1.1 : A.obj.obj U) + x.1.2) * x.2 = x.1.1 * x.2 + x.1.2 * x.2
    exact add_mul x.1.1 x.1.2 x.2

-- Sectionwise reconstruction follows `SheafRingObjectReconstruction`, with the
-- sheaf condition checked on a small model to retain independent site universes.
noncomputable section RingReconstruction

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
end RingReconstruction

private def unliftSetSheafIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} :
    sheafCompose J uliftFunctor.{w, w} ≅ 𝟭 (Sheaf J (Type w)) :=
  NatIso.ofComponents (fun T ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro T T' f; rfl)

-- The same conjugation by `ULift.down` is used in `LocalizationInverseImageCoherence`.
private noncomputable def inverseImageUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R S := by
  let eJ := unliftSetSheafIso (J := J)
  let eK := unliftSetSheafIso (J := K)
  let rR := (sheafCompose J (forget CommRingCat.{w})).obj R
  let rS := (sheafCompose K (forget CommRingCat.{w})).obj S
  let mR := SheafOfModules.toSheaf.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})
  let mS := SheafOfModules.toSheaf.{w}
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) ⋙
      sheafCompose K (forget AddCommGrpCat.{w})
  refine
    { ringUnderlying := L.mapIso (eJ.app rR) ≪≫ a.ringUnderlying ≪≫ (eK.app rS).symm
      modules := a.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft a.modules (Functor.isoWhiskerLeft mS eK) ≪≫
          a.moduleUnderlying ≪≫
            Functor.isoWhiskerRight (Functor.isoWhiskerLeft mR eJ.symm) L
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringAdd T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringMul T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringZero T (x ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringOne T (x ≫ eJ.hom.app rR) h W q
  · intro M T x y z h W q
    have h' := a.moduleAdd M T (x ≫ eJ.hom.app (mR.obj M))
      (y ≫ eJ.hom.app (mR.obj M)) (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T x h W q
    have h' := a.moduleZero M T (x ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T r x z h W q
    have h' := a.moduleSMul M T (r ≫ eJ.hom.app rR) (x ≫ eJ.hom.app (mR.obj M))
      (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl

end CategoryTheory.GeometricMorphism
