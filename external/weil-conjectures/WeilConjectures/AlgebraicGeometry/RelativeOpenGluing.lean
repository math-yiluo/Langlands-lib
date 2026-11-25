/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.AmbientOpenGluingObject
import WeilConjectures.AlgebraicGeometry.OpenUnionHomGluing

/-! # Relative two-open gluing without local finiteness conditions

Source: Stacks Project, Tag 08DG, Lemma cohomology-lemma-glue.
(blueprint: lem-sc-relative-open-gluing).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Assemble relative gluing from an ambient object and gluing of morphisms.
The compatibility calculation only uses functoriality and composition. -/
private theorem exists_relative_gluing_of_ambient
    {C D CW CV CI : Type*} [Category C] [Category D]
    [Category CW] [Category CV] [Category CI]
    (L : C ⥤ D) (JW : C ⥤ CW) (JV : C ⥤ CV) (JI : C ⥤ CI)
    (PW : D ⥤ CW) (PV : D ⥤ CV) (SW : CW ⥤ CI) (SV : CV ⥤ CI)
    (kW : L ⋙ PW ≅ JW) (kV : L ⋙ PV ≅ JV)
    (sW : JW ⋙ SW ≅ JI) (sV : JV ⋙ SV ≅ JI)
    {A : CW} {B : CV} (c : SW.obj A ≅ SV.obj B) (E : C)
    (a : A ⟶ JW.obj E) (b : B ⟶ JV.obj E)
    (hab : SW.map a ≫ sW.hom.app E = c.hom ≫ SV.map b ≫ sV.hom.app E)
    (hobj : ∃ (G : C) (jW : JW.obj G ≅ A) (jV : JV.obj G ≅ B),
      sW.inv.app G ≫ SW.map jW.hom ≫ c.hom = sV.inv.app G ≫ SV.map jV.hom)
    (hhom : ∀ (G : C) (a' : JW.obj G ⟶ JW.obj E) (b' : JV.obj G ⟶ JV.obj E),
      sW.inv.app G ≫ SW.map a' ≫ sW.hom.app E =
        sV.inv.app G ≫ SV.map b' ≫ sV.hom.app E →
      ∃ (α : L.obj G ⟶ L.obj E),
        PW.map α ≫ kW.hom.app E = kW.hom.app G ≫ a' ∧
        PV.map α ≫ kV.hom.app E = kV.hom.app G ≫ b') :
    ∃ (F : D) (α : F ⟶ L.obj E) (iW : PW.obj F ≅ A) (iV : PV.obj F ≅ B),
      PW.map α ≫ kW.hom.app E = iW.hom ≫ a ∧
      PV.map α ≫ kV.hom.app E = iV.hom ≫ b := by
  obtain ⟨G, jW, jV, ht⟩ := hobj
  have hcompat : sW.inv.app G ≫ SW.map (jW.hom ≫ a) ≫ sW.hom.app E =
      sV.inv.app G ≫ SV.map (jV.hom ≫ b) ≫ sV.hom.app E := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hab]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ SV.map b ≫ sV.hom.app E) ht
  obtain ⟨α, hW, hV⟩ := hhom G (jW.hom ≫ a) (jV.hom ≫ b) hcompat
  refine ⟨L.obj G, α, kW.app G ≪≫ jW, kV.app G ≪≫ jV, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.app_hom, Category.assoc] using hW
  · simpa only [Iso.trans_hom, Iso.app_hom, Category.assoc] using hV

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Glue derived objects and compatible maps on the union, using ambient relative
restriction. No perfectness or support is asserted.
Source: Stacks Project, Tag 08DG, Lemma cohomology-lemma-glue.
(blueprint: lem-sc-relative-open-gluing).

Proof: Apply exists_ambient_open_gluing_object to obtain G on X and local
isomorphisms jW, jV with their overlap transition equation. Compose them with
a and b. Expand functoriality on these composites, substitute the assumed
compatibility of a and b, and postcompose the transition equation with SV(b)
and sV(E). This gives compatible local maps between the fixed objects G and E.
Apply exists_open_union_hom to obtain alpha on Y = W union V. Set F = L(G),
iW = kW(G) followed by jW and iV = kV(G) followed by jV. Reassociating the
two restriction equations for alpha gives exactly the required equations.
No witnesses are chosen to define data elsewhere: this is an existential theorem.
The argument uses all derived complexes, with no boundedness, perfectness,
quasi-coherence, quasi-compactness or support assumptions. Empty opens and empty
Y are included by the two input theorems. -/
theorem exists_relative_open_gluing
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory W.toScheme) (B : schemeDerivedCategory V.toScheme) :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    ∀ (c : SW.obj A ≅ SV.obj B) (E : schemeDerivedCategory X)
      (a : A ⟶ JW.obj E) (b : B ⟶ JV.obj E),
      SW.map a ≫ sW.hom.app E = c.hom ≫ SV.map b ≫ sV.hom.app E →
      ∃ (F : schemeDerivedCategory (W ⊔ V).toScheme) (α : F ⟶ L.obj E),
        ∃ (iW : PW.obj F ≅ A) (iV : PV.obj F ≅ B),
          PW.map α ≫ kW.hom.app E = iW.hom ≫ a ∧
          PV.map α ≫ kV.hom.app E = iV.hom ≫ b := by
  intro L JW JV PW PV SW SV kW kV sW sV c E a b hab
  exact exists_relative_gluing_of_ambient L JW JV
    (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory PW PV SW SV kW kV sW sV
    c E a b hab (exists_ambient_open_gluing_object X W V A B c)
    (fun G ↦ exists_open_union_hom X W V G E)

end AlgebraicGeometry.Scheme
