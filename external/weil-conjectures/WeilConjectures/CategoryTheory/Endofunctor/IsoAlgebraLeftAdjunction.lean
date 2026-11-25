/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-!
# Lifting a left adjoint of a functor which has a lifted right adjoint

Let `L ⊣ R ⊣ L'` be adjunctions between categories with endofunctors `F` and `G`, with
commutation isomorphisms `eL : L ⋙ G ≅ F ⋙ L`, `eR : R ⋙ F ≅ G ⋙ R` and
`eL' : L' ⋙ G ≅ F ⋙ L'`, such that `R ⊣ L'` lifts to algebras with invertible structure
morphism (the mate of `eR⁻¹` is `eL'`). Suppose given a natural transformation `ι : L ⟶ L'`
compatible with `eL` and `eL'`, whose transpose under `L ⊣ R` is the inverse of the counit of
`R ⊣ L'` (as for the comparison `j_! ⟶ j_*` along an open immersion `j`). Then the unit and the
counit of `L ⊣ R` are compatible with the structure morphisms, so that `L ⊣ R` lifts to algebras
with invertible structure morphism
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction`), without computing the mate
of `eL⁻¹`.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : C ⥤ C} {G : D ⥤ D}

lemma mapOfNatIso_obj_obj_str_eq {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L) (K : IsoAlgebra F) :
    ((mapOfNatIso e).obj K).obj.str = e.hom.app K.carrier ≫ L.map K.obj.str := by
  rw [← str_hom, mapOfNatIso_obj_str]
  rfl

variable {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : R ⊣ L') [IsIso adj'.counit]
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R) (eL' : L' ⋙ G ≅ F ⋙ L')
  (h' : (mateEquiv adj' adj' (TwoSquare.mk _ _ _ _ eR.inv)) = eL'.hom)
  (ι : L ⟶ L') (hι : Functor.whiskerRight ι G ≫ eL'.hom = eL.hom ≫ Functor.whiskerLeft F ι)
  (hηι : ∀ K : C, adj.unit.app K ≫ R.map (ι.app K) = inv (adj'.counit.app K))

include hι hηι in
lemma map_unit_app_comp_eq_of_lowerStar [IsIso adj.unit] (X : C) (s : F.obj X ⟶ X)
    (hc : F.map (adj'.counit.app X) ≫ s =
      (eR.hom.app (L'.obj X) ≫ R.map (eL'.hom.app X ≫ L'.map s)) ≫ adj'.counit.app X) :
    F.map (adj.unit.app X) ≫ eR.hom.app (L.obj X) ≫ R.map (eL.hom.app X ≫ L.map s) =
      s ≫ adj.unit.app X := by
  have hRι : IsIso (R.map (ι.app X)) := by
    have := hηι X
    rw [← IsIso.eq_inv_comp] at this
    rw [this]
    infer_instance
  rw [← cancel_mono (R.map (ι.app X))]
  have n₁ := ι.naturality s
  have n₂ := NatTrans.congr_app hι X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at n₂
  have n₃ := eR.hom.naturality (ι.app X)
  simp only [Functor.comp_map] at n₃
  simp only [Category.assoc, ← Functor.map_comp]
  rw [n₁, ← reassoc_of% n₂, Functor.map_comp, ← reassoc_of% n₃, ← Functor.map_comp_assoc,
    hηι]
  rw [← cancel_mono (adj'.counit.app X)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc (eR.hom.app _), ← hc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

include hι hηι in
lemma map_unit_app_comp_eq_unit_app_of_lowerStar' [IsIso adj.unit] (X : C) (s : F.obj X ⟶ X)
    [IsIso s]
    (hc : F.map (adj'.counit.app X) ≫ s =
      (eR.hom.app (L'.obj X) ≫ R.map (eL'.hom.app X ≫ L'.map s)) ≫ adj'.counit.app X) :
    F.map (adj.unit.app X) ≫ eR.hom.app (L.obj X) ≫ R.map (eL.hom.app X) =
      adj.unit.app (F.obj X) := by
  have h := map_unit_app_comp_eq_of_lowerStar adj adj' eL eR eL' ι hι hηι X s hc
  have n := adj.unit.naturality s
  simp only [Functor.comp_map, Functor.id_map] at n
  rw [← cancel_mono (R.map (L.map s)), Category.assoc, Category.assoc, ← Functor.map_comp, h,
    ← n]

lemma map_counit_app_comp_eq_of_unit (X : D) (t : G.obj X ⟶ X)
    (hu : F.map (adj.unit.app (R.obj X)) ≫ eR.hom.app (L.obj (R.obj X)) ≫
      R.map (eL.hom.app (R.obj X)) = adj.unit.app (F.obj (R.obj X))) :
    G.map (adj.counit.app X) ≫ t =
      (eL.hom.app (R.obj X) ≫ L.map (eR.hom.app X ≫ R.map t)) ≫ adj.counit.app X := by
  rw [← cancel_epi (eL.inv.app (R.obj X))]
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have n₁ := eR.hom.naturality (adj.counit.app X)
  simp only [Functor.comp_map] at n₁
  have n₂ : (eR.hom.app X ≫ R.map t) ≫ adj.unit.app (R.obj X) =
      adj.unit.app (F.obj (R.obj X)) ≫ R.map (L.map (eR.hom.app X ≫ R.map t)) :=
    adj.unit.naturality _
  have hR : adj.unit.app (F.obj (R.obj X)) ≫ R.map (eL.inv.app (R.obj X) ≫
      (eL.hom.app (R.obj X) ≫ L.map (eR.hom.app X ≫ R.map t)) ≫ adj.counit.app X) =
      eR.hom.app X ≫ R.map t := by
    rw [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp, ← Category.assoc, ← n₂,
      Category.assoc, Adjunction.right_triangle_components, Category.comp_id]
  have hL : adj.unit.app (F.obj (R.obj X)) ≫
      R.map (eL.inv.app (R.obj X) ≫ G.map (adj.counit.app X) ≫ t) =
      eR.hom.app X ≫ R.map t := by
    rw [← hu]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc R (eL.hom.app _), Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, ← reassoc_of% n₁,
      ← Functor.map_comp_assoc F, Adjunction.right_triangle_components]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hR, hL]

include h' hι hηι in
/-- The unit of `L ⊣ R` intertwines the structure morphisms. -/
lemma map_unit_app_comp_str_of_lowerStar [IsIso adj.unit] (K : IsoAlgebra F) :
    F.map (adj.unit.app K.carrier) ≫
        ((mapOfNatIso eR).obj ((mapOfNatIso eL).obj K)).obj.str =
      K.obj.str ≫ adj.unit.app K.carrier := by
  have hc := map_counit_app_comp_str adj' eR eL' h' K
  rw [mapOfNatIso_obj_obj_str_eq, mapOfNatIso_obj_obj_str_eq] at hc ⊢
  exact map_unit_app_comp_eq_of_lowerStar adj adj' eL eR eL' ι hι hηι K.carrier K.obj.str hc

include h' hι hηι in
/-- The counit of `L ⊣ R` intertwines the structure morphisms. -/
lemma map_counit_app_comp_str_of_lowerStar [IsIso adj.unit] (M : IsoAlgebra G) :
    G.map (adj.counit.app M.carrier) ≫ M.obj.str =
      ((mapOfNatIso eL).obj ((mapOfNatIso eR).obj M)).obj.str ≫ adj.counit.app M.carrier := by
  have hc := map_counit_app_comp_str adj' eR eL' h' ((mapOfNatIso eR).obj M)
  rw [mapOfNatIso_obj_obj_str_eq, mapOfNatIso_obj_obj_str_eq, mapOfNatIso_obj_obj_str_eq] at hc
  rw [mapOfNatIso_obj_obj_str_eq, mapOfNatIso_obj_obj_str_eq]
  have : IsIso M.obj.str := M.property
  exact map_counit_app_comp_eq_of_unit adj eL eR M.carrier M.obj.str
    (map_unit_app_comp_eq_unit_app_of_lowerStar' adj adj' eL eR eL' ι hι hηι _ _ hc)

/-- **Lifting a left adjoint to algebras.** Under the assumptions of this file, the transports
along `L` and `R` of algebras with invertible structure morphism are adjoint, with the unit and
the counit of `L ⊣ R`. -/
noncomputable def mapOfNatIsoLeftAdjunction [IsIso adj.unit] :
    mapOfNatIso eL ⊣ mapOfNatIso eR :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app K := ObjectProperty.homMk
            ⟨adj.unit.app K.carrier,
              map_unit_app_comp_str_of_lowerStar adj adj' eL eR eL' h' ι hι hηι K⟩
          naturality _ _ f :=
            ObjectProperty.hom_ext _ (Algebra.Hom.ext (adj.unit.naturality f.hom.f)) }
      counit :=
        { app M := ObjectProperty.homMk
            ⟨adj.counit.app M.carrier,
              map_counit_app_comp_str_of_lowerStar adj adj' eL eR eL' h' ι hι hηι M⟩
          naturality _ _ f :=
            ObjectProperty.hom_ext _ (Algebra.Hom.ext (adj.counit.naturality f.hom.f)) }
      left_triangle := by
        ext K
        refine ObjectProperty.hom_ext _ (Algebra.Hom.ext ?_)
        simp
      right_triangle := by
        ext M
        refine ObjectProperty.hom_ext _ (Algebra.Hom.ext ?_)
        simp }

@[simp]
lemma mapOfNatIsoLeftAdjunction_unit_app_hom_f [IsIso adj.unit] (K : IsoAlgebra F) :
    ((mapOfNatIsoLeftAdjunction adj adj' eL eR eL' h' ι hι hηι).unit.app K).hom.f =
      adj.unit.app K.carrier :=
  rfl

@[simp]
lemma mapOfNatIsoLeftAdjunction_counit_app_hom_f [IsIso adj.unit] (M : IsoAlgebra G) :
    ((mapOfNatIsoLeftAdjunction adj adj' eL eR eL' h' ι hι hηι).counit.app M).hom.f =
      adj.counit.app M.carrier :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra
