/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# The right derived functor of a fully faithful functor

Let `F : C ⥤ D` be an additive functor between abelian categories which preserves K-injective
complexes, `C` having K-injective resolutions. If `F` is fully faithful, then so is its total
right derived functor `R(F) : D(C) ⥤ D(D)`.

Every object of `D(C)` is the image of a K-injective complex `I`, and morphisms in `D(C)` into
the image of a K-injective complex `J` are homotopy classes of morphisms of complexes
(`CochainComplex.IsKInjective.Qh_map_bijective`). Since `R(F)` is computed on `I` by applying
`F` termwise and `F J` is again K-injective, the map induced by `R(F)` on morphisms is identified
with the map induced by `F` on homotopy classes, which is bijective because `F` is fully
faithful.

## Main statements

- `CategoryTheory.Functor.rightDerivedFunctor_map_bijective_of_isKInjective`: `R(F)` is bijective
  on morphisms between images of K-injective complexes.
- `CategoryTheory.Functor.full_rightDerivedFunctor`,
  `CategoryTheory.Functor.faithful_rightDerivedFunctor`: `R(F)` is fully faithful.
- `CategoryTheory.Functor.preservesKInjectiveComplexes_of_iso`,
  `CategoryTheory.Functor.preservesKInjectiveComplexes_comp`: preserving K-injective complexes
  is invariant under isomorphism of functors and stable under composition.
-/

@[expose] public section

open CategoryTheory Abelian

namespace CategoryTheory.Functor

section PreservesKInjective

variable {C D E : Type*} [Category C] [Abelian C] [Category D] [Abelian D] [Category E]
  [Abelian E]

/-- Preserving K-injective complexes is invariant under isomorphism of functors. -/
lemma preservesKInjectiveComplexes_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    [F.PreservesKInjectiveComplexes] : G.PreservesKInjectiveComplexes where
  isKInjective_map K _ :=
    CochainComplex.isKInjective_of_iso ((NatIso.mapHomologicalComplex e _).app K)

/-- A composite of functors preserving K-injective complexes preserves K-injective complexes. -/
instance preservesKInjectiveComplexes_comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] [G.PreservesKInjectiveComplexes] :
    (F ⋙ G).PreservesKInjectiveComplexes where
  isKInjective_map K _ := by
    have : CochainComplex.IsKInjective ((F.mapHomologicalComplex _ ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
      inferInstanceAs (CochainComplex.IsKInjective ((G.mapHomologicalComplex _).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    exact CochainComplex.isKInjective_of_iso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) _).app K)

end PreservesKInjective

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [F.PreservesKInjectiveComplexes] [F.Full] [F.Faithful]

/-- For a fully faithful `F` preserving K-injective complexes, the right derived functor `R(F)`
is bijective on morphisms `Qh I ⟶ Qh J` between K-injective complexes `I` and `J`: under the
unit of `R(F)`, an isomorphism at K-injective complexes, it is the map
`Hom_K(I, J) ⟶ Hom_K(F I, F J)` induced by `F` on homotopy classes. -/
lemma rightDerivedFunctor_map_bijective_of_isKInjective
    (I J : CochainComplex C ℤ) [I.IsKInjective] [J.IsKInjective] :
    Function.Bijective (F.rightDerivedFunctor.map :
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj J)) → _) := by
  set ρ := F.rightDerivedFunctorUnit
  have hcomp : (F.rightDerivedFunctor.map :
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj J)) → _) ∘
        DerivedCategory.Qh.map =
      (fun g ↦ CategoryTheory.inv (ρ.app _) ≫ g ≫ ρ.app _) ∘ DerivedCategory.Qh.map ∘
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map := by
    ext φ
    simp only [Function.comp_apply]
    rw [IsIso.eq_inv_comp]
    exact (ρ.naturality φ).symm
  have h₁ := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J
  have h₂ := CochainComplex.IsKInjective.Qh_map_bijective
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj I))
    ((F.mapHomologicalComplex _).obj J)
  have h₃ : Function.Bijective (fun g : DerivedCategory.Qh.obj
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj I)) ⟶
        DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj J)) ↦
        CategoryTheory.inv (ρ.app _) ≫ g ≫ ρ.app _) :=
    (Iso.homCongr (asIso (ρ.app _)) (asIso (ρ.app _))).bijective
  have h₄ : Function.Bijective ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map :
      ((HomotopyCategory.quotient _ _).obj I ⟶ (HomotopyCategory.quotient _ _).obj J) → _) :=
    ⟨(F.mapHomotopyCategory _).map_injective, (F.mapHomotopyCategory _).map_surjective⟩
  exact (Function.Bijective.of_comp_iff _ h₁).1 (hcomp ▸ h₃.comp (h₂.comp h₄))

/-- For a fully faithful `F` preserving K-injective complexes, `R(F)` is bijective on all
morphisms, every object of the derived category being the image of a K-injective complex. -/
lemma rightDerivedFunctor_map_bijective (X Y : DerivedCategory C) :
    Function.Bijective (F.rightDerivedFunctor.map : (X ⟶ Y) → _) := by
  obtain ⟨I, _, ⟨eX⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  obtain ⟨J, _, ⟨eY⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective Y
  let eX' := eX ≪≫ ((DerivedCategory.quotientCompQhIso C).app I).symm
  let eY' := eY ≪≫ ((DerivedCategory.quotientCompQhIso C).app J).symm
  have h := ((Iso.homCongr (F.rightDerivedFunctor.mapIso eX')
    (F.rightDerivedFunctor.mapIso eY')).symm.bijective).comp
      ((rightDerivedFunctor_map_bijective_of_isKInjective F I J).comp
        (Iso.homCongr eX' eY').bijective)
  convert h using 1
  ext f
  simp

/-- The right derived functor of a fully faithful functor preserving K-injective complexes is
full. -/
instance full_rightDerivedFunctor : F.rightDerivedFunctor.Full :=
  ⟨fun f ↦ (rightDerivedFunctor_map_bijective F _ _).2 f⟩

/-- The right derived functor of a fully faithful functor preserving K-injective complexes is
faithful. -/
instance faithful_rightDerivedFunctor : F.rightDerivedFunctor.Faithful :=
  ⟨fun h ↦ (rightDerivedFunctor_map_bijective F _ _).1 h⟩

end CategoryTheory.Functor
