/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence

/-! # Adjunction transport with specified comparison formulas

Source: the final comparison paragraph of sk-prop-geo-p1-adjunction.proof.md,
in literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-the-cycle-class-of-a-divisor-and-the-projective-line/
sk-prop-geo-p1-adjunction/ (blueprint: geo-p1-adjunction-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.GeoP1Adjunction

set_option linter.flexible false in
/-- Transport an adjunction across equivalences, retaining both canonical formulas.
Source: the final comparison paragraph of sk-prop-geo-p1-adjunction.proof.md
(blueprint: geo-p1-adjunction-transport).

Proof: compose the inverse source equivalence adjunction, the given adjunction,
and the target equivalence adjunction. The two comparison isomorphisms and the
counits of the equivalences identify its functors with the desired functors.
Transport along these isomorphisms. For the unit formula, use naturality of both
comparisons and the given unit, followed by the two equivalence triangle laws.
For the counit formula, naturality moves the equivalence units across the comparisons;
the inverse comparison components cancel. The equivalence triangle laws and
naturality of the original counit reduce the composite to its stated image. -/
theorem transportAdjunction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ C') (F : D ≌ D')
    (L : C ⥤ D) (R : D ⥤ C) (L' : C' ⥤ D') (R' : D' ⥤ C')
    (a : L ⊣ R) (e : L ⋙ F.functor ≅ E.functor ⋙ L')
    (r : R ⋙ E.functor ≅ F.functor ⋙ R') :
    ∃ b : L' ⊣ R',
      (∀ X, E.functor.map (a.unit.app X) ≫ r.hom.app (L.obj X) ≫
        R'.map (e.hom.app X) = b.unit.app (E.functor.obj X)) ∧
      (∀ Y, e.hom.app (R.obj Y) ≫ L'.map (r.hom.app Y) ≫
        b.counit.app (F.functor.obj Y) = F.functor.map (a.counit.app Y)) := by
  let a₀ := (E.symm.toAdjunction.comp a).comp F.toAdjunction
  let el : (E.inverse ⋙ L) ⋙ F.functor ≅ L' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse e ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso L' ≪≫ L'.leftUnitor
  let er : F.inverse ⋙ (R ⋙ E.functor) ≅ R' :=
    Functor.isoWhiskerLeft F.inverse r ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.counitIso R' ≪≫ R'.leftUnitor
  let b := (a₀.ofNatIsoLeft el).ofNatIsoRight er
  have hrnat {Y Z : D} (f : Y ⟶ Z) {W : C'} (g : R'.obj (F.functor.obj Z) ⟶ W) :
      E.functor.map (R.map f) ≫ r.hom.app Z ≫ g =
        r.hom.app Y ≫ R'.map (F.functor.map f) ≫ g :=
    r.hom.naturality_assoc f g
  have henat {X Y : C} (f : X ⟶ Y) :
      F.functor.map (L.map f) ≫ e.hom.app Y =
        e.hom.app X ≫ L'.map (E.functor.map f) := e.hom.naturality f
  have hη {X Y : C} (f : X ⟶ Y) :
      E.functor.map f ≫ E.functor.map (a.unit.app Y) ≫ r.hom.app (L.obj Y) ≫
          R'.map (e.hom.app Y) =
        E.functor.map (a.unit.app X) ≫ r.hom.app (L.obj X) ≫
          R'.map (e.hom.app X) ≫ R'.map (L'.map (E.functor.map f)) := by
    have ha : f ≫ a.unit.app Y = a.unit.app X ≫ R.map (L.map f) :=
      a.unit.naturality f
    rw [← E.functor.map_comp_assoc, ha, E.functor.map_comp, Category.assoc, hrnat,
      ← R'.map_comp, henat f, R'.map_comp]
  refine ⟨b, ?_, ?_⟩
  · intro X
    simp [b, Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      a₀, Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
      el, er, Iso.trans_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.leftUnitor_hom_app,
      Functor.comp_map, Category.assoc, Equivalence.symm_unit]
    rw [hrnat, hrnat, hrnat]
    simp only [← R'.map_comp]
    rw [F.counit_naturality, F.counit_naturality_assoc, F.functor_unit_comp_assoc]
    simp only [R'.map_comp]
    rw [E.counitInv_app_functor]
    have h := hη (E.unitInv.app X)
    simp only [← E.counit_app_functor, Functor.id_obj, Functor.comp_obj] at h
    rw [← h, ← Category.assoc]
    simp
  · intro Y
    simp [b, Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      a₀, Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
      el, er, Iso.trans_inv, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.leftUnitor_inv_app,
      Functor.map_comp, Functor.comp_map, Category.assoc,
      Equivalence.symm_counit]
    have hr := r.hom.naturality (F.unit.app Y)
    simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hr
    have hc1 : r.hom.app Y ≫ R'.map (F.counitInv.app (F.functor.obj Y)) ≫
        r.inv.app (F.inverse.obj (F.functor.obj Y)) =
        E.functor.map (R.map (F.unit.app Y)) := by
      rw [F.counitInv_app_functor, ← Category.assoc, ← hr]
      simp
    slice_lhs 2 4 =>
      rw [← L'.map_comp, ← L'.map_comp, hc1]
    have he := henat (R.map (F.unit.app Y))
    simp only [Functor.id_obj, Functor.comp_obj] at he
    simp only [Category.assoc]
    slice_lhs 1 2 => rw [← he]
    simp only [Category.assoc]
    rw [E.counitInv_app_functor]
    have he₂ := henat (E.unit.app (R.obj (F.inverse.obj (F.functor.obj Y))))
    simp only [Functor.id_obj, Functor.comp_obj] at he₂
    slice_lhs 2 3 => rw [← he₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    slice_lhs 2 3 =>
      rw [← F.functor.map_comp, ← L.map_comp]
      simp
    simp only [Category.id_comp]
    have ha : L.map (R.map (F.unit.app Y)) ≫
        a.counit.app (F.inverse.obj (F.functor.obj Y)) =
        a.counit.app Y ≫ F.unit.app Y := a.counit.naturality (F.unit.app Y)
    rw [← F.functor.map_comp_assoc, ha, F.functor.map_comp]
    simpa only [Category.assoc, Category.comp_id, Functor.id_obj, Functor.comp_obj] using
      congrArg (fun z ↦ F.functor.map (a.counit.app Y) ≫ z) (F.functor_unit_comp Y)
end AlgebraicGeometry.ProEtale.GeoP1Adjunction
