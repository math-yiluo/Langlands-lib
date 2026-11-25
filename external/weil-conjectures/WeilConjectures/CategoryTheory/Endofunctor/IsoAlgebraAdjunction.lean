/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Adjunctions between categories of algebras with invertible structure morphism

Let `L ⊣ R` be an adjunction between `C` and `D`, and let `F : C ⥤ C` and `G : D ⥤ D` be
endofunctors together with exchange isomorphisms `eL : L ⋙ G ≅ F ⋙ L` and
`eR : R ⋙ F ≅ G ⋙ R`. If `eR` is the mate of `eL⁻¹`, the unit and the counit of `L ⊣ R` are
compatible with the transported structure morphisms, and the transports
`IsoAlgebra.mapOfNatIso eL ⊣ IsoAlgebra.mapOfNatIso eR` are again adjoint
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`).

If `F` and `G` are equivalences, the mate of `eL⁻¹` is an isomorphism
(`CategoryTheory.Endofunctor.IsoAlgebra.mateIso`), so every `eL` lifts `L ⊣ R`.

## Main declarations

- `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`: the lifted adjunction.
- `CategoryTheory.Endofunctor.IsoAlgebra.mateIso`: the mate of `eL⁻¹`, an isomorphism when `F`
  and `G` are equivalences.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : C ⥤ C} {G : D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) = eR.hom)

include h in
/-- The unit of `L ⊣ R` intertwines the structure morphism of an algebra with that of its
transport along `L` and then `R`. -/
lemma map_unit_app_comp_str (K : IsoAlgebra F) :
    F.map (adj.unit.app K.carrier) ≫
        ((mapOfNatIso eR).obj ((mapOfNatIso eL).obj K)).obj.str =
      K.obj.str ≫ adj.unit.app K.carrier := by
  have hu := unit_mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv) K.carrier
  rw [NatTrans.congr_app h] at hu
  have hs : ((mapOfNatIso eR).obj ((mapOfNatIso eL).obj K)).obj.str =
      eR.hom.app (L.obj K.carrier) ≫ R.map (eL.hom.app K.carrier ≫ L.map K.obj.str) := by
    rw [← str_hom, mapOfNatIso_obj_str]
    simp [← str_hom, mapOfNatIso_obj_str]
  rw [hs, reassoc_of% hu]
  simp only [Functor.comp_obj, Functor.id_obj]
  rw [← R.map_comp, Iso.inv_hom_id_app_assoc]
  exact adj.unit_naturality K.obj.str

include h in
/-- The counit of `L ⊣ R` intertwines the structure morphism of an algebra with that of its
transport along `R` and then `L`. -/
lemma map_counit_app_comp_str (M : IsoAlgebra G) :
    G.map (adj.counit.app M.carrier) ≫ M.obj.str =
      ((mapOfNatIso eL).obj ((mapOfNatIso eR).obj M)).obj.str ≫ adj.counit.app M.carrier := by
  have hc := mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ eL.inv) M.carrier
  rw [NatTrans.congr_app h] at hc
  have hs : ((mapOfNatIso eL).obj ((mapOfNatIso eR).obj M)).obj.str =
      eL.hom.app (R.obj M.carrier) ≫ L.map (eR.hom.app M.carrier ≫ R.map M.obj.str) := by
    rw [← str_hom, mapOfNatIso_obj_str]
    simp [← str_hom, mapOfNatIso_obj_str]
  have hn : L.map (R.map M.obj.str) ≫ adj.counit.app M.carrier =
      adj.counit.app (G.obj M.carrier) ≫ M.obj.str :=
    adj.counit_naturality M.obj.str
  simp only [hs, Functor.map_comp, Category.assoc]
  rw [hn]
  rw [reassoc_of% hc]
  simp

/-- **Lifting an adjunction to algebras.** If the exchange isomorphism `eR` of the right adjoint
is the mate of the inverse of the exchange isomorphism `eL` of the left adjoint, the transports
along `L` and `R` of algebras with invertible structure morphism are adjoint, with the unit and
the counit of `L ⊣ R`. -/
noncomputable def mapOfNatIsoAdjunction : mapOfNatIso eL ⊣ mapOfNatIso eR :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app K := ObjectProperty.homMk
            ⟨adj.unit.app K.carrier, map_unit_app_comp_str adj eL eR h K⟩
          naturality _ _ f :=
            ObjectProperty.hom_ext _ (Algebra.Hom.ext (adj.unit.naturality f.hom.f)) }
      counit :=
        { app M := ObjectProperty.homMk
            ⟨adj.counit.app M.carrier, map_counit_app_comp_str adj eL eR h M⟩
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
lemma mapOfNatIsoAdjunction_unit_app_hom_f (K : IsoAlgebra F) :
    ((mapOfNatIsoAdjunction adj eL eR h).unit.app K).hom.f = adj.unit.app K.carrier :=
  rfl

@[simp]
lemma mapOfNatIsoAdjunction_counit_app_hom_f (M : IsoAlgebra G) :
    ((mapOfNatIsoAdjunction adj eL eR h).counit.app M).hom.f = adj.counit.app M.carrier :=
  rfl

/-- The forgetful functor maps the unit of the lifted adjunction to the unit of `L ⊣ R`. -/
lemma forget_map_mapOfNatIsoAdjunction_unit_app (K : IsoAlgebra F) :
    (forget F).map ((mapOfNatIsoAdjunction adj eL eR h).unit.app K) = adj.unit.app K.carrier :=
  rfl

/-- The forgetful functor maps the counit of the lifted adjunction to the counit of `L ⊣ R`. -/
lemma forget_map_mapOfNatIsoAdjunction_counit_app (M : IsoAlgebra G) :
    (forget G).map ((mapOfNatIsoAdjunction adj eL eR h).counit.app M) =
      adj.counit.app M.carrier :=
  rfl

/-- If the counit of `L ⊣ R` is an isomorphism, so is the counit of the lifted adjunction. -/
instance isIso_mapOfNatIsoAdjunction_counit [IsIso adj.counit] :
    IsIso (mapOfNatIsoAdjunction adj eL eR h).counit := by
  have (M : IsoAlgebra G) : IsIso ((mapOfNatIsoAdjunction adj eL eR h).counit.app M) := by
    have : IsIso ((forget G).map ((mapOfNatIsoAdjunction adj eL eR h).counit.app M)) := by
      rw [forget_map_mapOfNatIsoAdjunction_counit_app]
      exact NatIso.isIso_app_of_isIso adj.counit _
    exact isIso_of_reflects_iso _ (forget G)
  exact NatIso.isIso_of_isIso_app _

/-- If the unit of `L ⊣ R` is an isomorphism, so is the unit of the lifted adjunction. -/
instance isIso_mapOfNatIsoAdjunction_unit [IsIso adj.unit] :
    IsIso (mapOfNatIsoAdjunction adj eL eR h).unit := by
  have (K : IsoAlgebra F) : IsIso ((mapOfNatIsoAdjunction adj eL eR h).unit.app K) := by
    have : IsIso ((forget F).map ((mapOfNatIsoAdjunction adj eL eR h).unit.app K)) := by
      rw [forget_map_mapOfNatIsoAdjunction_unit_app]
      exact NatIso.isIso_app_of_isIso adj.unit _
    exact isIso_of_reflects_iso _ (forget F)
  exact NatIso.isIso_of_isIso_app _

section Equivalence

variable [F.IsEquivalence] [G.IsEquivalence]

/-- If `F` and `G` are equivalences, the mate `R ⋙ F ⟶ G ⋙ R` of `eL⁻¹` is an isomorphism: its
mate along the adjunctions `F ⊣ F⁻¹` and `G ⊣ G⁻¹` is the conjugate of `eL⁻¹`
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), an isomorphism, and the units and counits
of these adjunctions are isomorphisms. -/
instance isIso_mateEquiv : IsIso (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) := by
  have hγ : IsIso (mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction
      (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv))) := by
    erw [iterated_mateEquiv_conjugateEquiv adj adj F.asEquivalence.toAdjunction
      G.asEquivalence.toAdjunction (TwoSquare.mk _ _ _ _ eL.inv)]
    exact conjugateEquiv_iso _ _ (α := (eL.inv : F ⋙ L ⟶ L ⋙ G))
  set β := mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)
  set γ := mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction β
  have hβ : β = (mateEquiv G.asEquivalence.toAdjunction F.asEquivalence.toAdjunction).symm γ :=
    ((mateEquiv _ _).symm_apply_apply β).symm
  have (Y : D) : IsIso (β.app Y) := by
    rw [hβ]
    have : ∀ Z, IsIso (γ.app Z) := fun Z ↦ @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hγ Z
    simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.comp_obj,
      Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id, Functor.map_id,
      Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit]
    have h1 : IsIso ((R ⋙ F.asEquivalence.functor).map (G.asEquivalence.unit.app Y)) :=
      inferInstance
    have h2 : IsIso (F.asEquivalence.counit.app (R.obj (G.asEquivalence.functor.obj Y))) :=
      inferInstance
    repeat' refine IsIso.comp_isIso' ?_ ?_
    all_goals first | exact IsIso.id _ | exact h1 | exact h2 | exact Functor.map_isIso _ _
  exact NatIso.isIso_of_isIso_app _

/-- If `F` and `G` are equivalences, the mate `R ⋙ F ≅ G ⋙ R` of `eL⁻¹`. Its hom is the mate
of `eL⁻¹` by definition, so `L ⊣ R` lifts along `eL` and `mateIso adj eL`
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`). -/
noncomputable def mateIso : R ⋙ F ≅ G ⋙ R :=
  asIso (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv))

lemma mateEquiv_natTrans_eq_mateIso_hom :
    (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) = (mateIso adj eL).hom :=
  rfl


end Equivalence

end CategoryTheory.Endofunctor.IsoAlgebra
