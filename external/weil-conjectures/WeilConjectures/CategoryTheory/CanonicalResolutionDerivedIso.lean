/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
(blueprint: lem-pc-grothendieck-resolution-unit-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The augmentation of the prescribed injective resolution, inverted after localization.
Source: Stacks Project, Tag 015M.
(blueprint: def-pc-canonical-resolution-derived-iso). -/
noncomputable def resolutionAugmentationIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
    {X : A} (I : InjectiveResolution X) :
    (DerivedCategory.Plus.singleFunctor A 0).obj X ≅
      DerivedCategory.Plus.Q.obj ⟨I.cochainComplex, 0, inferInstance⟩ :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app X ≪≫
      asIso (DerivedCategory.Q.map I.ι'))

/-- Apply the derived functor to the augmentation and invert its unit on injectives.
Source: Stacks Project, Tag 015M.
(blueprint: def-pc-canonical-resolution-derived-iso). -/
noncomputable def resolutionDerivedIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] {X : A} (I : InjectiveResolution X) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      DerivedCategory.Plus.Q.obj
        ⟨(F.mapHomologicalComplex _).obj I.cochainComplex, 0, inferInstance⟩ :=
  let L : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
  have : ∀ n, Injective (L.obj.X n) := fun n ↦
    inferInstanceAs (Injective (I.cochainComplex.X n))
  F.rightDerivedFunctorPlus.mapIso (resolutionAugmentationIso I) ≪≫
    F.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.quotientCompQhIso A).app L).symm ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj L))).symm ≪≫
    (DerivedCategory.Plus.quotientCompQhIso B).app (F.mapCochainComplexPlus.obj L)

/-- Canonical comparison with the extension of the natural-number-indexed complex F(I).
It is constructed from the augmentation, the inverse derived unit on injectives, and the
map/extension comparison; no witness of an unproved existence theorem is chosen.
Source: Stacks Project, Tag 015M.
(blueprint: def-pc-canonical-resolution-derived-iso). -/
noncomputable def canonicalResolutionDerivedIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] {X : A} (I : InjectiveResolution X) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      DerivedCategory.Plus.Q.obj
        ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat, 0, inferInstance⟩ :=
  resolutionDerivedIso F I ≪≫ DerivedCategory.Plus.Q.mapIso
    ((CochainComplex.plus B).isoMk
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F))

end CategoryTheory
