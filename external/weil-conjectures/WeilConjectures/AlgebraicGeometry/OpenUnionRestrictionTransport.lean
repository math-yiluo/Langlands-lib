/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram

/-! # Transport the restriction diagram to covering opens of an open union

Source: Stacks Project, Tag 08BW, restriction to the union before applying exactness.
(blueprint: lem-sc-open-union-restriction-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.mapDerivedCategory schemeDerivedOpenRestrictionCompIso

private theorem comparison_conjugation
    {B C D F : Type*} [Category B] [Category C] [Category D] [Category F]
    (e : B ⥤ C) [e.Full] [e.Faithful]
    (S : B ⥤ D) (H : D ⥤ F) (R : C ⥤ F) (c : S ⋙ H ≅ e ⋙ R)
    {B₀ B₁ : B} {D₀ D₁ : D} {C₀ C₁ : C} {F₀ F₁ : F}
    (t₀ : D₀ ≅ S.obj B₀) (t₁ : D₁ ≅ S.obj B₁)
    (r₀ : e.obj B₀ ≅ C₀) (r₁ : e.obj B₁ ≅ C₁)
    (s₀ : R.obj C₀ ≅ F₀) (s₁ : R.obj C₁ ≅ F₁)
    (z₀ : H.obj D₀ ≅ F₀) (z₁ : H.obj D₁ ≅ F₁)
    (h₀ : H.map t₀.hom ≫ c.hom.app B₀ ≫ R.map r₀.hom ≫ s₀.hom = z₀.hom)
    (h₁ : H.map t₁.hom ≫ c.hom.app B₁ ≫ R.map r₁.hom ≫ s₁.hom = z₁.hom)
    (f : C₀ ⟶ C₁) :
    H.map (t₀.hom ≫ S.map (e.preimage (r₀.hom ≫ f ≫ r₁.inv)) ≫ t₁.inv) =
      z₀.hom ≫ s₀.inv ≫ R.map f ≫ s₁.hom ≫ z₁.inv := by
  apply (cancel_mono z₁.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = H.map t₀.hom ≫ H.map (S.map (e.preimage (r₀.hom ≫ f ≫ r₁.inv))) ≫
        c.hom.app B₁ ≫ R.map r₁.hom ≫ s₁.hom := by
      rw [← h₁]
      simp only [Functor.map_comp, Category.assoc]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
    _ = H.map t₀.hom ≫ c.hom.app B₀ ≫
        R.map (e.map (e.preimage (r₀.hom ≫ f ≫ r₁.inv))) ≫
        R.map r₁.hom ≫ s₁.hom := by
      have hc := c.hom.naturality (e.preimage (r₀.hom ≫ f ≫ r₁.inv))
      dsimp only [Functor.comp_map] at hc
      simpa only [Category.assoc] using congrArg
        (fun j ↦ H.map t₀.hom ≫ j ≫ R.map r₁.hom ≫ s₁.hom) hc
    _ = H.map t₀.hom ≫ c.hom.app B₀ ≫ R.map r₀.hom ≫ R.map f ≫ s₁.hom := by
      simp only [Functor.map_preimage, Functor.map_comp, Category.assoc]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
    _ = z₀.hom ≫ s₀.inv ≫ R.map f ≫ s₁.hom := by
      rw [← h₀]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem comparison_pair
    {B C B' C' D F : Type*}
    [Category B] [Category C] [Category B'] [Category C'] [Category D] [Category F]
    (e : B ⥤ C) [e.Full] [e.Faithful]
    (e' : B' ⥤ C') [e'.Full] [e'.Faithful]
    (S : B ⥤ D) (S' : B' ⥤ D) (H : D ⥤ F) [H.Faithful]
    (R : C ⥤ F) (R' : C' ⥤ F)
    (c : S ⋙ H ≅ e ⋙ R) (c' : S' ⋙ H ≅ e' ⋙ R')
    {B₀ B₁ : B} {B₀' B₁' : B'} {D₀ D₁ : D}
    {C₀ C₁ : C} {C₀' C₁' : C'} {F₀ F₁ : F}
    (t₀ : D₀ ≅ S.obj B₀) (t₁ : D₁ ≅ S.obj B₁)
    (t₀' : D₀ ≅ S'.obj B₀') (t₁' : D₁ ≅ S'.obj B₁')
    (r₀ : e.obj B₀ ≅ C₀) (r₁ : e.obj B₁ ≅ C₁)
    (r₀' : e'.obj B₀' ≅ C₀') (r₁' : e'.obj B₁' ≅ C₁')
    (s₀ : R.obj C₀ ≅ F₀) (s₁ : R.obj C₁ ≅ F₁)
    (s₀' : R'.obj C₀' ≅ F₀) (s₁' : R'.obj C₁' ≅ F₁)
    (z₀ : H.obj D₀ ≅ F₀) (z₁ : H.obj D₁ ≅ F₁)
    (h₀ : H.map t₀.hom ≫ c.hom.app B₀ ≫ R.map r₀.hom ≫ s₀.hom = z₀.hom)
    (h₁ : H.map t₁.hom ≫ c.hom.app B₁ ≫ R.map r₁.hom ≫ s₁.hom = z₁.hom)
    (h₀' : H.map t₀'.hom ≫ c'.hom.app B₀' ≫ R'.map r₀'.hom ≫ s₀'.hom = z₀.hom)
    (h₁' : H.map t₁'.hom ≫ c'.hom.app B₁' ≫ R'.map r₁'.hom ≫ s₁'.hom = z₁.hom)
    (f : C₀ ⟶ C₁) (f' : C₀' ⟶ C₁')
    (h : s₀.inv ≫ R.map f ≫ s₁.hom = s₀'.inv ≫ R'.map f' ≫ s₁'.hom) :
    t₀.hom ≫ S.map (e.preimage (r₀.hom ≫ f ≫ r₁.inv)) ≫ t₁.inv =
      t₀'.hom ≫ S'.map (e'.preimage (r₀'.hom ≫ f' ≫ r₁'.inv)) ≫ t₁'.inv := by
  apply H.map_injective
  rw [comparison_conjugation e S H R c t₀ t₁ r₀ r₁ s₀ s₁ z₀ z₁ h₀ h₁,
    comparison_conjugation e' S' H R' c' t₀' t₁' r₀' r₁' s₀' s₁' z₀ z₁ h₀' h₁']
  simpa only [Category.assoc] using congrArg (fun j ↦ z₀.hom ≫ j ≫ z₁.inv) h

-- Keep the isomorphism-component calculation abstract so it never unfolds derived restrictions.
private theorem comparison_diagram_pair
    {A Y B C B' C' D F : Type*}
    [Category A] [Category Y] [Category B] [Category C]
    [Category B'] [Category C'] [Category D] [Category F]
    (L : A ⥤ Y) (JW : A ⥤ C) (JV : A ⥤ C')
    (PW : Y ⥤ C) (PV : Y ⥤ C') (SW : C ⥤ F) (SV : C' ⥤ F)
    (RU : Y ⥤ B) (RT : Y ⥤ B') (SU : B ⥤ D) (ST : B' ⥤ D)
    (RI : Y ⥤ D) (JI : A ⥤ F)
    (eW : B ≌ C) (eV : B' ≌ C') (eI : D ≌ F)
    (tU : RU ⋙ SU ≅ RI) (tT : RT ⋙ ST ≅ RI)
    (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV)
    (kW : L ⋙ PW ≅ JW) (kV : L ⋙ PV ≅ JV)
    (sW : JW ⋙ SW ≅ JI) (sV : JV ⋙ SV ≅ JI)
    (cW : SU ⋙ eI.functor ≅ eW.functor ⋙ SW)
    (cV : ST ⋙ eI.functor ≅ eV.functor ⋙ SV)
    (qI : (L ⋙ RI) ⋙ eI.functor ≅ JI)
    (hW : ∀ G : A,
      eI.functor.map (tU.inv.app (L.obj G)) ≫ cW.hom.app (RU.obj (L.obj G)) ≫
        SW.map (qW.hom.app (L.obj G)) ≫ SW.map (kW.hom.app G) ≫ sW.hom.app G =
          qI.hom.app G)
    (hV : ∀ G : A,
      eI.functor.map (tT.inv.app (L.obj G)) ≫ cV.hom.app (RT.obj (L.obj G)) ≫
        SV.map (qV.hom.app (L.obj G)) ≫ SV.map (kV.hom.app G) ≫ sV.hom.app G =
          qI.hom.app G)
    (G E : A) (a : JW.obj G ⟶ JW.obj E) (b : JV.obj G ⟶ JV.obj E)
    (hab : sW.inv.app G ≫ SW.map a ≫ sW.hom.app E =
      sV.inv.app G ≫ SV.map b ≫ sV.hom.app E) :
    let a' := eW.functor.preimage
      (qW.hom.app (L.obj G) ≫ kW.hom.app G ≫ a ≫
        kW.inv.app E ≫ qW.inv.app (L.obj E))
    let b' := eV.functor.preimage
      (qV.hom.app (L.obj G) ≫ kV.hom.app G ≫ b ≫
        kV.inv.app E ≫ qV.inv.app (L.obj E))
    tU.inv.app (L.obj G) ≫ SU.map a' ≫ tU.hom.app (L.obj E) =
      tT.inv.app (L.obj G) ≫ ST.map b' ≫ tT.hom.app (L.obj E) := by
  have hp := comparison_pair eW.functor eV.functor SU ST eI.functor SW SV cW cV
    (tU.app (L.obj G)).symm (tU.app (L.obj E)).symm
    (tT.app (L.obj G)).symm (tT.app (L.obj E)).symm
    (qW.app (L.obj G) ≪≫ kW.app G) (qW.app (L.obj E) ≪≫ kW.app E)
    (qV.app (L.obj G) ≪≫ kV.app G) (qV.app (L.obj E) ≪≫ kV.app E)
    (sW.app G) (sW.app E) (sV.app G) (sV.app E) (qI.app G) (qI.app E)
    (by simpa only [Iso.symm_hom, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
        Functor.map_comp, Category.assoc] using hW G)
    (by simpa only [Iso.symm_hom, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
        Functor.map_comp, Category.assoc] using hW E)
    (by simpa only [Iso.symm_hom, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
        Functor.map_comp, Category.assoc] using hV G)
    (by simpa only [Iso.symm_hom, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
        Functor.map_comp, Category.assoc] using hV E) a b hab
  simpa only [Iso.symm_hom, Iso.symm_inv, Iso.trans_hom, Iso.trans_inv,
    Iso.app_hom, Iso.app_inv, Category.assoc] using hp

-- The existential localization data must remain inline for the following let-bound functors.
set_option linter.style.haveILetI false in
-- Instantiating the categorical transport lemma needs many derived-functor type comparisons.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency true in
/-- The local restriction diagram on an ambient union is transported to an actual
cover of the union scheme. This statement supplies only equivalences, comparison
isomorphisms, and compatibility of local maps; it does not assert any gluing.
Source: Stacks Project, Tag 08BW, canonical restriction to the union; Mathlib's
`Modules.overMapCompOverEquiv`, `overFunctorEquiv`, `restrictFunctorComp` and
`restrictFunctorCongr` implement the change of open schemes.
(blueprint: lem-sc-open-union-restriction-transport).

Proof: Put Y = (W union V).toScheme and take U and T to be the inverse images
of W and V under the open inclusion Y into X. Inverse image preserves union,
and its inverse image of W union V is top, so U and T cover Y. Each pulled-back
open scheme is canonically isomorphic to the corresponding original open scheme,
as is their intersection. Transport module sheaves through these scheme
isomorphisms; their exact functors induce the displayed derived equivalences.
Supply localizations in Hom universe w by derivedOpenLocalization and the
localization transport in open_derived_localization_adjunction, applied with
Y's given localization. For qW and qV, identify both underived restriction routes
with restriction along W into Y and V into Y, respectively, using
Modules.overMapCompOverEquiv, overFunctorEquiv, restrictFunctorComp and
restrictFunctorCongr, and then derive these natural isomorphisms. The overlap
comparison is a pasted square of the same underived isomorphisms. On a complex,
the factorization identities for mapDerivedCategoryCompIso and
mapDerivedCategoryNatIso show that deriving this pasted square equals pasting
its derived comparisons; extend the identity through the localization using
Localization.natTrans_ext. Conjugate a and b by kW and kV and take their
preimages under the two derived equivalences. Apply the overlap equivalence to
the desired equality, use this pasted-square identity and functoriality, and
cancel the equivalence units and comparison inverse pairs. The remaining
equality is exactly the displayed ambient compatibility hypothesis. The same
argument includes empty opens, disjoint opens, and an empty union, since all
scheme identifications and equivalence identities hold in these cases. -/
theorem open_union_restriction_transport
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
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
      ∃ hU : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hU
      ∃ hT : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace)),
      letI := hT
      ∃ hI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings (U ⊓ T).toScheme.toRingedSpace)),
      letI := hI
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
      ∃ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∀ (G E : schemeDerivedCategory X)
        (a : JW.obj G ⟶ JW.obj E) (b : JV.obj G ⟶ JV.obj E),
        sW.inv.app G ≫ SW.map a ≫ sW.hom.app E =
          sV.inv.app G ≫ SV.map b ≫ sV.hom.app E →
        let a' := eW.functor.preimage
          (qW.hom.app (L.obj G) ≫ kW.hom.app G ≫ a ≫
            kW.inv.app E ≫ qW.inv.app (L.obj E))
        let b' := eV.functor.preimage
          (qV.hom.app (L.obj G) ≫ kV.hom.app G ≫ b ≫
            kV.inv.app E ≫ qV.inv.app (L.obj E))
        tU.inv.app (L.obj G) ≫ SU.map a' ≫ tU.hom.app (L.obj E) =
          tT.inv.app (L.obj G) ≫ ST.map b' ≫ tT.hom.app (L.obj E) := by
  intro L JW JV SW SV sW sV PW PV kW kV U T
  have h := open_union_restriction_comparison_diagram.{u, w} X W V
  refine h.imp ?_
  intro hU h
  letI := hU
  refine h.imp ?_
  intro hT h
  letI := hT
  refine h.imp ?_
  intro hI h
  letI := hI
  intro RU RT SU ST tU tT
  refine h.imp ?_
  intro eW h
  refine h.imp ?_
  intro eV h
  refine h.imp ?_
  intro qW h
  refine h.imp ?_
  intro qV h
  obtain ⟨eI, cW, cV, qI, hW, hV⟩ := h
  intro G E a b hab
  exact @comparison_diagram_pair
    (schemeDerivedCategory X) (schemeDerivedCategory (W ⊔ V).toScheme)
    (schemeDerivedCategory U.toScheme) (schemeDerivedCategory W.toScheme)
    (schemeDerivedCategory T.toScheme) (schemeDerivedCategory V.toScheme)
    (schemeDerivedCategory (U ⊓ T).toScheme) (schemeDerivedCategory (W ⊓ V).toScheme)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    L JW JV PW PV SW SV RU RT SU ST
    _ _ eW eV eI tU tT qW qV kW kV sW sV cW cV qI hW hV G E a b hab

end AlgebraicGeometry.Scheme
