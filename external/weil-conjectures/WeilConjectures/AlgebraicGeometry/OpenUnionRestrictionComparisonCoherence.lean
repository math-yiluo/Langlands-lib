/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent

/-! # Coherence of supplied open-union restriction comparisons

Source: Stacks Project Tags 08BW and 08BT; Mathlib restriction composition.
(blueprint: lem-sc-open-union-restriction-comparison-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem cancel_mapped_iso_pasting
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B : C} (t : A ≅ B)
    {Z : D} (f : F.obj B ⟶ Z) (g : F.obj A ⟶ Z)
    (h : g = F.map t.hom ≫ 𝟙 _ ≫ f) : F.map t.inv ≫ g = f := by
  rw [h, ← F.map_comp_assoc, t.inv_hom_id, F.map_id]
  exact (Category.id_comp (𝟙 _ ≫ f)).trans (Category.id_comp _)


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Supplied direct restriction comparisons descend to commuting overlap comparisons.
Source: Stacks Project Tag 08BW, cohomology.tex, lemma-mayer-vietoris-hom;
Tag 08BT, lemma-adjoint-lower-shriek-restrict.
(blueprint: lem-sc-open-union-restriction-comparison-coherence).

Proof: Treat each chain W intersect V into W into W union V, and W intersect V into
V into W union V separately. Direct restriction through the inverse image of W is a
localization: extension by zero is an exact left adjoint, its unit is invertible,
and exact derived functoriality derives that adjunction and unit. The unit is the
canonical restriction-of-extension map: on each stalk of the open it is the identity,
as in the proof of nonempty_openExtensionRestrictionIso. Transport through
Modules.overEquiv. By Localization.fullyFaithfulWhiskeringLeft, precomposition with
this restriction is fully faithful on functor categories. The canonical nested
restriction comparison identifies PW followed by SW with direct restriction from
the union to the intersection. Combine that comparison with the supplied qW, qIY
and the inverse of tU. Descend the resulting isomorphism uniquely to cW. Do the
same for V to obtain cV, using the same qIY and eI. Threefold restriction coherence
identifies SW(kW) followed by sW with the union-to-intersection comparison followed
by the ambient direct comparison. Underived, both composites restrict the same
section; cancel the overEquiv units and counits and use overFunctorMap. Derive this
identity using mapDerivedCategoryCompIso_fac, mapDerivedCategoryNatIso_fac and
Localization.natTrans_ext. Substitution into the defining identities for cW,cV
gives the two equations.
Define qI as the functor associator followed by qIY
whiskered with L and the canonical ambient intersection restriction comparison.
Its component is qIY(LG) followed by that ambient comparison, so the resulting
equations are precisely the asserted equations with qI. These arguments apply to empty,
disjoint, and repeated opens. No direct equivalences, localizations or direct comparisons
are constructed by this statement: they are supplied as inputs. -/
theorem open_union_restriction_comparison_coherence
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ W).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (((W ⊔ V).ι ⁻¹ᵁ W) ⊓ ((W ⊔ V).ι ⁻¹ᵁ V)).toScheme.toRingedSpace))]
    :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let U := (W ⊔ V).ι ⁻¹ᵁ W
    let T := (W ⊔ V).ι ⁻¹ᵁ V
      let RU := (schemeOpenRestriction (W ⊔ V).toScheme U).mapDerivedCategory
      let RT := (schemeOpenRestriction (W ⊔ V).toScheme T).mapDerivedCategory
      let SU := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)).mapDerivedCategory
      let ST := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)).mapDerivedCategory
      let tU := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)
      let tT := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)
      ∀ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∀ (eI : schemeDerivedCategory (U ⊓ T).toScheme ≌
          schemeDerivedCategory (W ⊓ V).toScheme)
        (_qIY : (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory ⋙
          eI.functor ≅ (schemeOpenOverlapRestriction X
            (homOfLE (inf_le_left.trans le_sup_left) : W ⊓ V ⟶ W ⊔ V)).mapDerivedCategory),
      ∃ (cW : SU ⋙ eI.functor ≅ eW.functor ⋙ SW)
        (cV : ST ⋙ eI.functor ≅ eV.functor ⋙ SV)
        (qI : (L ⋙ (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory) ⋙
          eI.functor ≅ (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory),
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tU.inv.app (L.obj G)) ≫ cW.hom.app (RU.obj (L.obj G)) ≫
          SW.map (qW.hom.app (L.obj G)) ≫ SW.map (kW.hom.app G) ≫ sW.hom.app G =
            qI.hom.app G) ∧
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tT.inv.app (L.obj G)) ≫ cV.hom.app (RT.obj (L.obj G)) ≫
          SV.map (qV.hom.app (L.obj G)) ≫ SV.map (kV.hom.app G) ≫ sV.hom.app G =
            qI.hom.app G) := by
  intro L SW SV sW sV PW PV kW kV U T RU RT SU ST tU tT eW eV qW qV eI qIY
  let RI := (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory
  let kI := schemeDerivedOpenRestrictionCompIso X
    (homOfLE (inf_le_left.trans le_sup_left) : W ⊓ V ⟶ W ⊔ V)
  let qI : (L ⋙ RI) ⋙ eI.functor ≅
      (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory :=
    Functor.associator L RI eI.functor ≪≫ Functor.isoWhiskerLeft L qIY ≪≫ kI
  let bWL : L ⋙ (RU ⋙ (SU ⋙ eI.functor)) ≅
      (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory :=
    Functor.isoWhiskerLeft L
      ((Functor.associator RU SU eI.functor).symm ≪≫
        Functor.isoWhiskerRight tU eI.functor) ≪≫
      (Functor.associator L RI eI.functor).symm ≪≫ qI
  let rW : L ⋙ (RU ⋙ eW.functor) ≅
      (schemeOpenRestriction X W).mapDerivedCategory :=
    Functor.isoWhiskerLeft L qW ≪≫ kW
  let bWR : L ⋙ (RU ⋙ (eW.functor ⋙ SW)) ≅
      (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory :=
    Functor.isoWhiskerLeft L (Functor.associator RU eW.functor SW).symm ≪≫
      (Functor.associator L (RU ⋙ eW.functor) SW).symm ≪≫
        Functor.isoWhiskerRight rW SW ≪≫ sW
  let bVL : L ⋙ (RT ⋙ (ST ⋙ eI.functor)) ≅
      (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory :=
    Functor.isoWhiskerLeft L
      ((Functor.associator RT ST eI.functor).symm ≪≫
        Functor.isoWhiskerRight tT eI.functor) ≪≫
      (Functor.associator L RI eI.functor).symm ≪≫ qI
  let rV : L ⋙ (RT ⋙ eV.functor) ≅
      (schemeOpenRestriction X V).mapDerivedCategory :=
    Functor.isoWhiskerLeft L qV ≪≫ kV
  let bVR : L ⋙ (RT ⋙ (eV.functor ⋙ SV)) ≅
      (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory :=
    Functor.isoWhiskerLeft L (Functor.associator RT eV.functor SV).symm ≪≫
      (Functor.associator L (RT ⋙ eV.functor) SV).symm ≪≫
        Functor.isoWhiskerRight rV SV ≪≫ sV
  have haW := derived_open_restriction_iso_descent X (W ⊔ V)
    (RU ⋙ (SU ⋙ eI.functor)) (RU ⋙ (eW.functor ⋙ SW)) (bWL ≪≫ bWR.symm)
  obtain ⟨aW, haW⟩ := haW
  have hcW := derived_open_restriction_iso_descent (W ⊔ V).toScheme U
    (SU ⋙ eI.functor) (eW.functor ⋙ SW) aW
  obtain ⟨cW, hcW⟩ := hcW
  have haV := derived_open_restriction_iso_descent X (W ⊔ V)
    (RT ⋙ (ST ⋙ eI.functor)) (RT ⋙ (eV.functor ⋙ SV)) (bVL ≪≫ bVR.symm)
  obtain ⟨aV, haV⟩ := haV
  have hcV := derived_open_restriction_iso_descent (W ⊔ V).toScheme T
    (ST ⋙ eI.functor) (eV.functor ⋙ SV) aV
  obtain ⟨cV, hcV⟩ := hcV
  refine ⟨cW, cV, qI, ?_, ?_⟩
  · intro G
    have hc := (congrArg (fun e ↦ e.hom.app (L.obj G)) hcW).trans
      (congrArg (fun e ↦ e.hom.app G) haW)
    simp only [Functor.isoWhiskerLeft_hom, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app] at hc
    have h := congrArg (fun f ↦ f ≫ bWR.hom.app G) hc
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
    simp only [bWR, bWL, rW, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.map_comp, Functor.comp_obj, Category.assoc, Category.id_comp] at h
    exact cancel_mapped_iso_pasting eI.functor (tU.app (L.obj G))
      (qI.hom.app G) _ h
  · intro G
    have hc := (congrArg (fun e ↦ e.hom.app (L.obj G)) hcV).trans
      (congrArg (fun e ↦ e.hom.app G) haV)
    simp only [Functor.isoWhiskerLeft_hom, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app] at hc
    have h := congrArg (fun f ↦ f ≫ bVR.hom.app G) hc
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
    simp only [bVR, bVL, rV, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.map_comp, Functor.comp_obj, Category.assoc, Category.id_comp] at h
    exact cancel_mapped_iso_pasting eI.functor (tT.app (L.obj G))
      (qI.hom.app G) _ h

end AlgebraicGeometry.Scheme
