/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Center.Localization

/-!
# Central endomorphisms on complexes and derived categories

An element `z` of the center of a category `C`, i.e. a natural endomorphism of the identity
functor, induces elements of the centers of the categories of homological complexes
(`CategoryTheory.CatCenter.mapHomologicalComplex`, acting degreewise) and of the derived category
(`CategoryTheory.CatCenter.derivedCategory`, by localization). We show:

* `CategoryTheory.CatCenter.derivedCategory_app_shift`: the induced central element of `D(C)`
  commutes with the shifts;
* `CategoryTheory.CatCenter.mapDerivedCategory_map_derivedCategory_app`: an exact functor
  `F : C ⥤ D` sending `z` to `z'` sends the induced central element of `D(C)` to that of `D(D)`;
* `CategoryTheory.Adjunction.map_catCenter_app`: if the right adjoint of an adjunction sends a
  central element `z'` to `z`, then the left adjoint sends `z` to `z'`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace CatCenter

variable {C D : Type*} [Category* C] [Category* D]

/-- The component of a central element at an object is the conjugate of its component at an
isomorphic object. -/
lemma app_eq_of_iso (z : CatCenter C) {X Y : C} (e : X ≅ Y) :
    z.app Y = e.inv ≫ z.app X ≫ e.hom := by
  rw [← z.naturality, Iso.inv_hom_id_assoc]

/-- The compatibility of a central element with a shift is invariant under isomorphisms. -/
lemma app_shift_of_iso {A : Type*} [AddMonoid A] [HasShift C A] (z : CatCenter C) {X Y : C}
    (e : X ≅ Y) (a : A) (h : z.app (X⟦a⟧) = (z.app X)⟦a⟧') : z.app (Y⟦a⟧) = (z.app Y)⟦a⟧' := by
  rw [z.app_eq_of_iso ((shiftFunctor C a).mapIso e), h, z.app_eq_of_iso e]
  simp

/-- The compatibility of a functor with central elements is invariant under isomorphisms. -/
lemma map_app_of_iso (F : C ⥤ D) (z : CatCenter C) (z' : CatCenter D) {X Y : C} (e : X ≅ Y)
    (h : F.map (z.app X) = z'.app (F.obj X)) : F.map (z.app Y) = z'.app (F.obj Y) := by
  rw [z.app_eq_of_iso e, z'.app_eq_of_iso (F.mapIso e), F.map_comp, F.map_comp, h]
  rfl

section HomologicalComplex

variable [HasZeroMorphisms C] {ι : Type*} (z : CatCenter C) (c : ComplexShape ι)

/-- The central element of the category of homological complexes acting degreewise as a central
element `z` of `C`. -/
noncomputable def mapHomologicalComplex : CatCenter (HomologicalComplex C c) where
  asHom.app K :=
    { f i := z.app (K.X i)
      comm' i j _ := (z.naturality (K.d i j)).symm }
  asHom.naturality K L φ := by
    ext i
    exact z.naturality (φ.f i)

@[simp]
lemma mapHomologicalComplex_app_f (K : HomologicalComplex C c) (i : ι) :
    ((z.mapHomologicalComplex c).app K).f i = z.app (K.X i) :=
  rfl

variable {z c} in
/-- A functor compatible with central elements is compatible with the induced central elements
on homological complexes. -/
lemma mapHomologicalComplex_map_app [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {z' : CatCenter D} (h : ∀ X : C, F.map (z.app X) = z'.app (F.obj X))
    (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c).map ((z.mapHomologicalComplex c).app K) =
      (z'.mapHomologicalComplex c).app ((F.mapHomologicalComplex c).obj K) := by
  ext i
  exact h (K.X i)

end HomologicalComplex

section CochainComplex

variable [Preadditive C] (z : CatCenter C)

/-- The degreewise central element of cochain complexes commutes with the shifts. -/
lemma mapHomologicalComplex_app_shift (K : CochainComplex C ℤ) (n : ℤ) :
    (z.mapHomologicalComplex (ComplexShape.up ℤ)).app (K⟦n⟧) =
      ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app K)⟦n⟧' := by
  ext i
  simp

end CochainComplex

section DerivedCategory

variable [Abelian C] [HasDerivedCategory C] (z : CatCenter C)

/-- The central element of the derived category induced by a central element `z` of `C`: it is
induced, through the localization functor, by the degreewise action of `z` on complexes. -/
noncomputable def derivedCategory : CatCenter (DerivedCategory C) :=
  (z.mapHomologicalComplex (ComplexShape.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

@[simp]
lemma derivedCategory_app_Q_obj (K : CochainComplex C ℤ) :
    z.derivedCategory.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app K) :=
  localization_app _ _ _ K

/-- The central element of the derived category induced by a central element of `C` commutes with
the shifts. -/
lemma derivedCategory_app_shift (K : DerivedCategory C) (n : ℤ) :
    z.derivedCategory.app (K⟦n⟧) = (z.derivedCategory.app K)⟦n⟧' := by
  refine z.derivedCategory.app_shift_of_iso (DerivedCategory.Q.objObjPreimageIso K) n ?_
  rw [← cancel_epi ((DerivedCategory.Q.commShiftIso n).hom.app _)]
  have h₁ : (DerivedCategory.Q.commShiftIso n).hom.app (DerivedCategory.Q.objPreimage K) ≫
      z.derivedCategory.app ((DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K))⟦n⟧) =
      z.derivedCategory.app (DerivedCategory.Q.obj ((DerivedCategory.Q.objPreimage K)⟦n⟧)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (DerivedCategory.Q.objPreimage K) :=
    z.derivedCategory.naturality _
  rw [h₁, derivedCategory_app_Q_obj, derivedCategory_app_Q_obj, mapHomologicalComplex_app_shift,
    Functor.commShiftIso_hom_naturality]

variable [Abelian D] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

variable {z} in
/-- An exact functor compatible with central elements `z` of `C` and `z'` of `D` is compatible
with the induced central elements of the derived categories. -/
lemma mapDerivedCategory_map_derivedCategory_app {z' : CatCenter D}
    (h : ∀ X : C, F.map (z.app X) = z'.app (F.obj X)) (K : DerivedCategory C) :
    F.mapDerivedCategory.map (z.derivedCategory.app K) =
      z'.derivedCategory.app (F.mapDerivedCategory.obj K) := by
  refine map_app_of_iso _ _ _ (DerivedCategory.Q.objObjPreimageIso K) ?_
  rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app _), derivedCategory_app_Q_obj]
  have := F.mapDerivedCategoryFactors.hom.naturality
    ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app (DerivedCategory.Q.objPreimage K))
  dsimp at this
  rw [this, mapHomologicalComplex_map_app F h, ← derivedCategory_app_Q_obj, CatCenter.naturality]

end DerivedCategory

end CatCenter

/-- If the right adjoint `G` of an adjunction `F ⊣ G` sends a central element `z'` to `z`, then
the left adjoint `F` sends `z` to `z'`. -/
lemma Adjunction.map_catCenter_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {z : CatCenter C} {z' : CatCenter D}
    (h : ∀ Y : D, G.map (z'.app Y) = z.app (G.obj Y)) (X : C) :
    F.map (z.app X) = z'.app (F.obj X) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h]
  exact (adj.unit.naturality (z.app X)).symm.trans (z.naturality (adj.unit.app X)).symm

end CategoryTheory
