/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Symmetric tensor structure on sheaves

Source: blueprint `det-def-sfb-sheaf-tensor-structure` and Stacks Tags 00WH, 0H7J.

The tensor is the sheafification of the objectwise presheaf tensor.  The canonical
localized symmetric structure and the canonical strong monoidal and braided structures
on sheafification are packaged together here.
-/

@[expose] public section

universe vC uC w vA uA

open CategoryTheory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- The symmetric tensor structure on sheaves obtained by sheafifying the objectwise tensor,
with the canonical strong symmetric monoidal sheafification functor.

The symmetric structure is `Sheaf.symmetricCategory`; its tensor object is therefore the
localization tensor, namely the sheafification of the objectwise tensor.  The final two fields
record the canonical monoidal and braided structures on `presheafToSheaf`, whose tensorator
is thus the specified comparison between sheafified tensors.
(blueprint: det-def-sfb-sheaf-tensor-structure)
-/
structure SfbSheafTensorStructure
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] where
  monoidal : MonoidalCategory (Sheaf J A)
  symmetric : @SymmetricCategory (Sheaf J A) _ monoidal
  sheafificationMonoidal :
    @Functor.Monoidal (Cᵒᵖ ⥤ A) _ _ (Sheaf J A) _ monoidal
      (presheafToSheaf J A)
  sheafificationBraided :
    @Functor.Braided (Cᵒᵖ ⥤ A) _ _ _ (Sheaf J A) _ monoidal symmetric.toBraidedCategory
      (presheafToSheaf J A)

/-- The canonical symmetric sheaf tensor structure.
(blueprint: det-def-sfb-sheaf-tensor-structure) -/
noncomputable def sfbSheafTensorStructure
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] : SfbSheafTensorStructure (A := A) J := by
  let h := presheaf_enrichedHoms_exist (C := C) (A := A)
  letI : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A F G := h.1
  letI : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A F G := h.2
  let m : MonoidalCategory (Sheaf J A) := Sheaf.monoidalCategory J A
  letI : MonoidalCategory (Sheaf J A) := m
  let s : @SymmetricCategory (Sheaf J A) _ m := Sheaf.symmetricCategory J A
  letI : SymmetricCategory (Sheaf J A) := s
  exact
    { monoidal := m
      symmetric := s
      sheafificationMonoidal := inferInstance
      sheafificationBraided := inferInstance }

end CategoryTheory
