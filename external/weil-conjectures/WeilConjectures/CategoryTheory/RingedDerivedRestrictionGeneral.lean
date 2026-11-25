/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Derived slice restriction with independent universes

Source: Stacks Project, Modules on Sites, Section 03DH (including Tag 03DJ);
Cohomology on Sites, Tag 08JB
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r m w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Exactness of the existing slice module restriction, with independent sizes.
Source: Stacks, Modules on Sites, Section 03DH (localization of ringed sites)
(auxiliary; not a blueprint node).
Proof: restriction evaluates on the objects of the slice, so preserves addition and
kernels. A covering of an object of the slice is exactly a covering of its underlying
object. Consequently local lifts of sections of an epimorphism remain local lifts
on the slice. Restriction therefore preserves cokernels, and is additive and exact.
The abelian exactness criterion gives preservation of finite limits and colimits. -/
theorem ringedOverFunctor_exactGeneral (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}] :
    (SheafOfModules.overFunctor.{m} R U).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overFunctor.{m} R U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{m} R U) := by
  let F := SheafOfModules.overFunctor.{m} R U
  let G := SheafOfModules.toSheaf.{m} (R.over U)
  let H := J.overPullback AddCommGrpCat.{m} U
  have : F.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  let e : F ⋙ G ≅ SheafOfModules.toSheaf.{m} R ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  have : H.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{m} f).2 hf
    have : Sheaf.IsLocallySurjective (H.map f) :=
      Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) f.hom
    exact Sheaf.epi_of_isLocallySurjective (H.map f)
  have : F.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    apply G.epi_of_epi_map
    exact inferInstanceAs (Epi (H.map ((SheafOfModules.toSheaf.{m} R).map f)))
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  have : HasFiniteBiproducts (SheafOfModules.{m} R) := Abelian.hasFiniteBiproducts
  have : HasFiniteCoproducts (SheafOfModules.{m} R) :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  exact ⟨inferInstance, inferInstance, Functor.preservesFiniteColimits_of_preservesHomology F⟩

/-- The functor on derived categories induced by the actual exact slice restriction.
Source: Stacks 03DH and 08JB (auxiliary; not a blueprint node).
For commutative ring sheaves, apply this to their underlying ring sheaves. -/
def ringedDerivedRestrictionGeneral (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasDerivedCategory.{w} (SheafOfModules.{m} R)]
    [HasDerivedCategory.{w'} (SheafOfModules.{m} (R.over U))] :
    DerivedCategory (SheafOfModules.{m} R) ⥤
      DerivedCategory (SheafOfModules.{m} (R.over U)) :=
  haveI := (ringedOverFunctor_exactGeneral R U).1
  haveI := (ringedOverFunctor_exactGeneral R U).2.1
  haveI := (ringedOverFunctor_exactGeneral R U).2.2
  (SheafOfModules.overFunctor.{m} R U).mapDerivedCategory

/-- Slice restriction when the coefficient universe contains the site data. All
sheafification instances are supplied canonically, before elaborating its consumers.
Source: Stacks 03DH and 08JB (auxiliary; not a blueprint node). -/
def ringedDerivedRestrictionSized {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (S : Sheaf J RingCat.{max u v}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{max u v} S)]
    [HasDerivedCategory.{w'} (SheafOfModules.{max u v} (S.over U))] :
    DerivedCategory (SheafOfModules.{max u v} S) ⥤
      DerivedCategory (SheafOfModules.{max u v} (S.over U)) :=
  ringedDerivedRestrictionGeneral.{u, v, max u v, max u v, w, w'} S U

end CategoryTheory
