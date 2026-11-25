/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-!
# The right derived functor on the unbounded derived category is triangulated

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has K-injective
resolutions. The localization functor restricts to an equivalence
`HomotopyCategory.KInjectives.equivalence C : K(Inj) ≌ D(C)` between the homotopy category of
K-injective complexes, a triangulated subcategory of `K(C)`, and the derived category; it is a
triangulated equivalence. The right derived functor `F.rightDerivedFunctor` identifies with the
inverse of this equivalence followed by `F` applied termwise
(`CategoryTheory.Functor.rightDerivedFunctorIsoKInjectives`), and the shift and triangulated
structures are transported along this isomorphism, as for
`CategoryTheory.Functor.rightDerivedFunctorPlus`.

## Main results

- `CategoryTheory.Functor.rightDerivedFunctor`, with `CommShift ℤ` and `IsTriangulated`
  instances.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace HomotopyCategory.KInjectives

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [HasKInjectiveResolutions C]

instance : (ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal ⋙
    DerivedCategory.Qh).IsEquivalence :=
  inferInstanceAs (Qh (C := C)).IsEquivalence

variable (C) in
/-- The equivalence between the homotopy category of K-injective complexes and the derived
category, induced by the localization functor. -/
noncomputable abbrev equivalence : KInjectives C ≌ DerivedCategory C :=
  (ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal ⋙ DerivedCategory.Qh).asEquivalence

noncomputable instance : (equivalence C).functor.CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.ι _ ⋙ DerivedCategory.Qh).CommShift ℤ)

instance : (equivalence C).functor.IsTriangulated :=
  inferInstanceAs ((ObjectProperty.ι _ ⋙ DerivedCategory.Qh).IsTriangulated)

noncomputable instance : (equivalence C).inverse.CommShift ℤ :=
  (equivalence C).commShiftInverse ℤ

instance : (equivalence C).CommShift ℤ :=
  (equivalence C).commShift_of_functor ℤ

instance : (equivalence C).IsTriangulated :=
  .mk' _ inferInstance

end HomotopyCategory.KInjectives

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

open HomotopyCategory in
/-- The right derived functor of `F` identifies with the inverse of the equivalence
`K(Inj) ≌ D(C)` followed by `F` applied termwise. -/
noncomputable def rightDerivedFunctorIsoKInjectives :
    F.rightDerivedFunctor ≅ (KInjectives.equivalence C).inverse ⋙ ObjectProperty.ι _ ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  have : IsIso (whiskerLeft (ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by
      obtain ⟨K, _, rfl⟩ := KInjectives.mk_surjective X
      dsimp
      infer_instance)
  let α : ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (KInjectives.equivalence C).functor ⋙ F.rightDerivedFunctor :=
    asIso (whiskerLeft (ObjectProperty.ι (subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit) ≪≫
      (Functor.associator _ _ _).symm
  (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (KInjectives.equivalence C).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ α.symm

noncomputable instance : F.rightDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso F.rightDerivedFunctorIsoKInjectives.symm ℤ

instance : F.rightDerivedFunctor.IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  exact Functor.isTriangulated_of_iso F.rightDerivedFunctorIsoKInjectives.symm

end CategoryTheory.Functor
