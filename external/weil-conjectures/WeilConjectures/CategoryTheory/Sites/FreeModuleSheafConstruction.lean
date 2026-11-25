/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits


/-!
# Free modules on arbitrary sheaves of generators

Source: Stacks Project, Modules on Sites, Tags 04BL, 03CY, 03D3 and 08TQ
(auxiliary; not a blueprint node).

The free module is module sheafification of the sectionwise free module, on an arbitrary
sheaf of generators. Algebraic inverse-image presentations record precisely the transported
operations. Underlying modules use the common value universe of that recorded interface.
-/

@[expose] public section

universe w uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafFreeModule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

/-- Forget commutativity of the coefficient sheaf, using Mathlib's sheaf composition.
Source: Stacks 04BL (auxiliary; not a blueprint node). -/
abbrev ring (B : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B

/-- Underlying set sheaves of modules, with the lift used by algebraic inverse image.
Source: Stacks 03D2 (auxiliary; not a blueprint node). -/
noncomputable abbrev moduleSets (B : Sheaf J CommRingCat.{w}) :
    SheafOfModules.{w} (ring B) ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf (ring B) ⋙
    sheafCompose J (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})

/-- Module sheafification of `U ↦ B(U)[E(U)]`. Mathlib's presheaf free functor sends
restrictions to the semilinear extension of `[s] ↦ [s|V]`, and its map on generator
sheaves is the sectionwise linear extension. Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node). -/
noncomputable def free (B : Sheaf J CommRingCat.{w}) :
    Sheaf J (Type w) ⥤ SheafOfModules.{w} (ring B) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  sheafToPresheaf J (Type w) ⋙ PresheafOfModules.free (ring B).obj ⋙
    PresheafOfModules.sheafification (𝟙 (ring B).obj)

/-- The presheaf generator map followed by the abelian sheafification unit, before
lifting the underlying sets. Source: Stacks 04BL
(auxiliary; not a blueprint node). -/
noncomputable def generatorRaw (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (SheafOfModules.toSheaf (ring B) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).obj ((free B).obj E) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  { hom := PresheafOfModules.freeAdjunctionUnit (ring B).obj E.obj ≫
      Functor.whiskerRight
        (toSheafify J (PresheafOfModules.freeObj (R := (ring B).obj) E.obj).presheaf)
        (forget AddCommGrpCat.{w}) }

/-- The map `s ↦ [s]` into the underlying sheaf of the free module, with the harmless
`ULift` identification required by the recorded algebraic inverse-image interface.
Source: Stacks 04BL (auxiliary; not a blueprint node). -/
noncomputable def generator (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (moduleSets B).obj ((free B).obj E) where
  hom := (generatorRaw B E).hom ≫ Functor.whiskerLeft
    (((free B).obj E).val.presheaf ⋙ forget AddCommGrpCat.{w}) uliftFunctorTrivial.inv

/-- Simultaneous coefficient and generator change: the sheafified linear extension of
`[s] ↦ [e(s)]`, semilinear along `b`. It is constructed by the two recorded adjunctions,
with target scalars restricted along `b`. Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node). -/
noncomputable def change {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (free B).obj E ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj
        ((free B').obj E') :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj)).homEquiv _ _).symm
    (PresheafOfModules.freeObjDesc (e.hom ≫ (generatorRaw B' E').hom))

/-- The simultaneous change map on underlying lifted set sheaves.
Source: Stacks 04BL (auxiliary; not a blueprint node). -/
noncomputable def changeSets {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (moduleSets B).obj ((free B).obj E) ⟶ (moduleSets B').obj ((free B').obj E') :=
  (moduleSets B).map (change b e)

end CategoryTheory.SheafFreeModule
