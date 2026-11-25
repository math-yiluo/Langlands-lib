/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# The total left derived functor on the unbounded derived category

Let `C` be an abelian monoidal category which admits functorial flat
resolutions (`Abelian.HasFunctorialFlatResolution C`). By the K-flat
machinery migrated from mathlib PR #25848, the inclusion of the K-flat
complexes into the homotopy category is a left derivability structure
`(HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat` with
respect to quasi-isomorphisms.

Given an additive functor `F : C ⥤ D` to an abelian category `D`, the
only functor-specific input needed in order to derive `F` is that `F`
sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms.
We package this hypothesis as the type class `F.PreservesKFlatQuasiIso`.
From it we deduce the `LocalizerMorphism.Derives` property
(`Functor.derives_kFlat`) and define the total left derived functor

`F.leftDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D`

on the full unbounded derived categories, together with its counit
`F.leftDerivedFunctorCounit`, which is an isomorphism on K-flat
complexes. The lemma `Functor.isLeftDerivedFunctor_iff_isIso_app_of_kFlat`
characterizes the left derived functor uniquely: a functor equipped with
a counit is *the* left derived functor iff the counit is an isomorphism
on K-flat complexes.

This is the left analogue, via K-flat resolutions, of
`CategoryTheory.Functor.rightDerivedFunctor` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`.
It is designed so that the left derivation `Lf^*` of the inverse image
functor `f^*` on (étale) sheaves of modules can be obtained by
instantiating `C` and `D` with the relevant sheaf categories and proving
the single `PreservesKFlatQuasiIso` statement for `f^*`.

-/

@[expose] public section

universe uC uD vC vD wC wD

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable (F : C ⥤ D) [F.Additive]

/-- An additive functor `F : C ⥤ D` between abelian categories, where `C` is
monoidal, preserves K-flat quasi-isomorphisms if it sends quasi-isomorphisms
between K-flat cochain complexes to quasi-isomorphisms.

This is exactly the functor-specific hypothesis needed to left derive `F`
on the unbounded derived category using the K-flat left derivability
structure: see `Functor.leftDerivedFunctor`. For the inverse image functor
on sheaves of modules, this should be proved using the tensor/base-change
description of the pullback on K-flat complexes. -/
class PreservesKFlatQuasiIso : Prop where
  quasiIso_map {K L : CochainComplex C ℤ}
    (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K)
    (hL : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat L)
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)

lemma quasiIso_mapHomologicalComplex_map_of_kFlat [F.PreservesKFlatQuasiIso]
    {K L : CochainComplex C ℤ}
    (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K)
    (hL : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat L)
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  PreservesKFlatQuasiIso.quasiIso_map hK hL f

/-- An exact functor preserves all quasi-isomorphisms, in particular the
quasi-isomorphisms between K-flat complexes. -/
instance (priority := 100) [F.PreservesHomology] : F.PreservesKFlatQuasiIso where
  quasiIso_map _ _ _ := inferInstance

section

variable [HasDerivedCategory.{wD} D] [F.PreservesKFlatQuasiIso]

lemma isIso_Qh_map_mapHomotopyCategory_map
    {X Y : HomotopyCategory C (ComplexShape.up ℤ)}
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X)
    (hY : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat Y)
    (φ : X ⟶ Y) (hφ : HomotopyCategory.quasiIso C (ComplexShape.up ℤ) φ) :
    IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map φ)) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  rw [HomotopyCategory.kFlat_quotient_obj_iff] at hX hY
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff] at hφ
  have := F.quasiIso_mapHomologicalComplex_map_of_kFlat hX hY g
  rw [F.mapHomotopyCategory_map]
  exact Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) _ (by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff]
      exact this)

/-- If `F : C ⥤ D` preserves K-flat quasi-isomorphisms, then the composition
of the induced functor on homotopy categories with the localization functor
`DerivedCategory.Qh` is derivable with respect to the K-flat left
derivability structure. -/
lemma derives_kFlat :
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).localizerMorphismKFlat.Derives
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
  fun X Y _ hf ↦ F.isIso_Qh_map_mapHomotopyCategory_map X.property Y.property _ hf

end

section

variable [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [F.PreservesKFlatQuasiIso]

instance : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  F.derives_kFlat.hasLeftDerivedFunctor

/-- The total left derived functor `DerivedCategory C ⥤ DerivedCategory D`
of an additive functor `F : C ⥤ D` between abelian categories, where the
monoidal abelian category `C` admits functorial flat resolutions and `F`
preserves K-flat quasi-isomorphisms.

It is computed on a cochain complex by applying `F` to a K-flat resolution;
see `Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat`. -/
noncomputable def leftDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[inherit_doc leftDerivedFunctor]
scoped notation "L(" F ")" => leftDerivedFunctor F

/-- The counit natural transformation that is part of the data of the total
left derived functor `F.leftDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D`. -/
noncomputable def leftDerivedFunctorCounit :
    DerivedCategory.Qh ⋙ F.leftDerivedFunctor ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

instance : F.leftDerivedFunctor.IsLeftDerivedFunctor
    F.leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [leftDerivedFunctor, leftDerivedFunctorCounit]
  infer_instance

/-- On a K-flat complex, the counit of the total left derived functor of `F`
is an isomorphism: the left derived functor is computed by applying `F`. -/
lemma isIso_leftDerivedFunctorCounit_app_of_kFlat (K : CochainComplex C ℤ)
    (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    IsIso (F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :=
  F.derives_kFlat.isIso_of_isLeftDerivedFunctor F.leftDerivedFunctorCounit
    ⟨_, (HomotopyCategory.kFlat_quotient_obj_iff K).2 hK⟩

/-- A functor `LF : DerivedCategory C ⥤ DerivedCategory D` equipped with a
natural transformation `α : Qh ⋙ LF ⟶ F.mapHomotopyCategory _ ⋙ Qh` is the
total left derived functor of `F` iff `α` is an isomorphism on all K-flat
complexes. This characterizes `F.leftDerivedFunctor` uniquely and can be
used to identify it with other constructions. -/
lemma isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    {LF : DerivedCategory C ⥤ DerivedCategory D}
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ↔
      ∀ (K : CochainComplex C ℤ), (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K →
        IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) := by
  rw [F.derives_kFlat.isLeftDerivedFunctor_iff_isIso α]
  constructor
  · intro h K hK
    exact h ⟨_, (HomotopyCategory.kFlat_quotient_obj_iff K).2 hK⟩
  · rintro h ⟨X, hX⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact h K ((HomotopyCategory.kFlat_quotient_obj_iff K).1 hX)

end

end CategoryTheory.Functor
