/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Exact restriction and transport of strict-perfect packages

Source: Stacks Project, Modules on Sites, Tags 03DJ and 04IX.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' r m w w'
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

private theorem pushforward_finiteLimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [G.IsContinuous J K]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesFiniteLimits (pushforward.{m} φ) := by
  let T := forget.{m} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (pushforward.{m} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((forget.{m} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem pushforward_finiteColimits
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {G : C ⥤ D} [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{m}), G.op.HasPointwiseRightKanExtension F]
    {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    PreservesFiniteColimits (pushforward.{m} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{m} J K
  have : PreservesColimitsOfSize.{0, 0} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{m} J K).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (toSheaf.{m} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  let T := toSheaf.{m} S
  have : PreservesFiniteColimits (pushforward.{m} φ ⋙ T) := by
    change PreservesFiniteColimits (toSheaf.{m} R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- Restriction of module sheaves to a slice is exact, at independent universes.
Source: Stacks Project, Tag 03DJ. The forgetful comparison with abelian sheaf restriction
preserves and reflects the finite limit and colimit universal properties.
(auxiliary; not a blueprint node). -/
theorem overFunctor_exact_ofUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}] :
    PreservesFiniteLimits (overFunctor.{max u v r} R U) ∧
      PreservesFiniteColimits (overFunctor.{max u v r} R U) := by
  exact ⟨pushforward_finiteLimits (𝟙 _), pushforward_finiteColimits (𝟙 _)⟩

/-- Slice restriction adds module maps componentwise. Source: Stacks Project, Tag 03DJ.
(auxiliary; not a blueprint node). -/
instance sitePerfectOverFunctor_additive
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) : (overFunctor.{max u v r} R U).Additive :=
  ⟨fun {_ _} f g ↦ by ext W x; rfl⟩

/-- Further restriction adds module maps componentwise. Source: Stacks Project, Tag 04IX.
(auxiliary; not a blueprint node). -/
instance sitePerfectOverMap_additive
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {U V : C} (f : V ⟶ U) : (overMap.{max u v r} R f).Additive :=
  ⟨fun {_ _} g h ↦ by ext W x; rfl⟩

end SheafOfModules
