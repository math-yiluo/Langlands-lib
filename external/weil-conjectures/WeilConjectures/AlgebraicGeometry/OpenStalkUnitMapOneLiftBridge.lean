/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import all WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison

/-! # Transporting a supplied subscheme morphism to the open slice site

Source: Stacks Project, Sheaves Tag 00A0 (3).
(blueprint: new-lem-sc-open-stalk-unit-map-one-lift-bridge).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a subscheme morphism to the slice site, with its canonical germ formula.

Source: Stacks Project, Sheaves, Lemma 6.31.1, Tag 00A0 (2)-(3), including modules.
(blueprint: new-lem-sc-open-stalk-unit-map-one-lift-bridge).

Proof: Set V = U.ι ''ᵁ A, with hxV supplied by hxA and hVU by Opens.ι_image_le.
The isomorphism U.ι.isoImage A identifies A.toScheme with V.toScheme over U.
Restrict f along its inverse, and use restrictFunctorComp and restrictFunctorCongr
with (U.ι.isoImage A).inv ≫ A.ι = X.homOfLE hVU to identify the two restricted
sheaves with the restrictions to V of the original sheaves on U. Conjugate the
restricted f by these identifications and overMapCompOverEquiv; the fully faithful
functor (Modules.overEquiv V).functor then gives k. The canonical natural
restriction-stalk comparison gives a. Its linearity follows from the composition
of the open-immersion stalk ring maps and the germ scalar-action formula. For a
section m over B in A, all the comparison maps send its germ to the germ of the
same section under the corresponding image-open identification. Naturality of
restriction-stalk comparison with respect to f therefore gives the displayed
formula. This construction uses no prescribed map q on the stalk and no hypothesis
that f realizes such a map. It is just the slice transport and its germ formula. -/
private theorem exists_slice_hom_with_subscheme_germ_formula
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (F N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (A : U.toScheme.Opens) (hxA : (⟨x, hxU⟩ : U.toScheme) ∈ A)
    (f : (Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj F) ⟶
      (Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj N)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
      let S := openModuleStalkFunctor X V ⟨x, hxV⟩
      ∃ (a : R ⋙ S ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (k : R.obj F ⟶ R.obj N),
        ∀ (B : A.toScheme.Opens)
          (hxB : (⟨⟨x, hxU⟩, hxA⟩ : A.toScheme) ∈ B)
          (m : Γ((Modules.restrictFunctor A.ι).obj
            ((Modules.overEquiv U).functor.obj F), B)),
          a.hom.app N (S.map k (a.inv.app F
            (((Modules.overEquiv U).functor.obj F).presheaf.germ (A.ι ''ᵁ B)
              ⟨x, hxU⟩ ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m))) =
            ((Modules.overEquiv U).functor.obj N).presheaf.germ (A.ι ''ᵁ B)
              ⟨x, hxU⟩ ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ (Modules.Hom.app f B m) := by
  let V := U.ι ''ᵁ A
  have hxV : x ∈ V := ⟨⟨x, hxU⟩, hxA, rfl⟩
  have hVU : V ≤ U := U.ι_image_le A
  let y : A.toScheme := ⟨⟨x, hxU⟩, hxA⟩
  let v : V.toScheme := ⟨x, hxV⟩
  let e₀ := U.ι.isoImage A
  let e' : A.toScheme ⟶ V.toScheme := e₀.hom.copyBase
    (fun z ↦ ⟨z.1.1, ⟨z.1, z.2, rfl⟩⟩) (by
      ext z
      apply Subtype.ext
      have h := congrArg (fun f : A.toScheme ⟶ X ↦ f z)
        (Scheme.Hom.isoImage_hom_ι U.ι A)
      exact h)
  have he' : e' = e₀.hom := Scheme.Hom.copyBase_eq _ _ _
  have : IsIso e' := by rw [he']; infer_instance
  let e := asIso e'
  let j := X.homOfLE hVU
  have hej : e.hom ≫ j = A.ι := by
    apply (cancel_mono U.ι).mp
    change e' ≫ X.homOfLE hVU ≫ U.ι = A.ι ≫ U.ι
    rw [Scheme.homOfLE_ι, he']
    exact Scheme.Hom.isoImage_hom_ι U.ι A
  let E := (Modules.overEquiv U).functor
  let C := (Modules.overEquiv V).functor
  let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
  let H := Modules.restrictFunctor e.hom
  let H' := Modules.restrictFunctor e.inv
  let η : 𝟭 V.toScheme.Modules ≅ H ⋙ H' :=
    (Modules.restrictFunctorId (X := V.toScheme)).symm ≪≫
      (Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
      Modules.restrictFunctorComp e.inv e.hom
  let ε : H' ⋙ H ≅ 𝟭 A.toScheme.Modules :=
    (Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Modules.restrictFunctorId
  let d : V.toScheme.Modules ≌ A.toScheme.Modules := CategoryTheory.Equivalence.mk H H' η ε
  let D := C ⋙ d.functor
  let b : R ⋙ D ≅ E ⋙ Modules.restrictFunctor A.ι :=
    (Functor.associator R C H).symm ≪≫
      Functor.isoWhiskerRight (Modules.overMapCompOverEquiv (homOfLE hVU)) H ≪≫
      Functor.associator E (Modules.restrictFunctor j) H ≪≫
      Functor.isoWhiskerLeft E ((Modules.restrictFunctorComp e.hom j).symm ≪≫
        Modules.restrictFunctorCongr hej)
  let k : R.obj F ⟶ R.obj N := D.preimage (b.hom.app F ≫ f ≫ b.inv.app N)
  have hk : D.map k = b.hom.app F ≫ f ≫ b.inv.app N := D.map_preimage _
  let SA := RingedSpace.moduleStalkFunctor A.toScheme.toRingedSpace y
  let SV := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace v
  let SU := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨x, hxU⟩
  let Re := ModuleCat.restrictScalars (e.hom.stalkMap y).hom
  let Rv := ModuleCat.restrictScalars (V.ι.stalkMap v).hom
  let Ra := ModuleCat.restrictScalars (A.ι.stalkMap y).hom
  let Ru := ModuleCat.restrictScalars (U.ι.stalkMap ⟨x, hxU⟩).hom
  let ce : (H ⋙ SA) ⋙ Re ≅ SV := restrictionStalkLinearNatIso e.hom y
  let ca : (Modules.restrictFunctor A.ι ⋙ SA) ⋙ Ra ≅ SU :=
    restrictionStalkLinearNatIso A.ι y
  have hr : (e.hom.stalkMap y).hom.comp (V.ι.stalkMap v).hom =
      (A.ι.stalkMap y).hom.comp (U.ι.stalkMap ⟨x, hxU⟩).hom := by
    have heι : e.hom ≫ V.ι = A.ι ≫ U.ι := by
      simpa only [e, asIso_hom, he'] using Scheme.Hom.isoImage_hom_ι U.ι A
    have h := Scheme.Hom.stalkMap_congr_hom (e.hom ≫ V.ι) (A.ι ≫ U.ι) heι y
    rw [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl] at h
    have h' : (e.hom ≫ V.ι).stalkMap y = (A.ι ≫ U.ι).stalkMap y :=
      h.trans (Category.id_comp _)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h'
    exact congrArg CommRingCat.Hom.hom h'
  let r : Re ⋙ Rv ≅ Ra ⋙ Ru :=
    (ModuleCat.restrictScalarsComp _ _).symm ≪≫
      ModuleCat.restrictScalarsCongr hr ≪≫ ModuleCat.restrictScalarsComp _ _
  let c : D ⋙ SA ⋙ Re ⋙ Rv ≅ C ⋙ SV ⋙ Rv :=
    Functor.associator C H (SA ⋙ Re ⋙ Rv) ≪≫
      Functor.isoWhiskerLeft C (
        (Functor.associator H SA (Re ⋙ Rv)).symm ≪≫
        (Functor.associator (H ⋙ SA) Re Rv).symm ≪≫
        Functor.isoWhiskerRight ce Rv)
  let a : R ⋙ (C ⋙ SV ⋙ Rv) ≅ E ⋙ SU ⋙ Ru :=
    Functor.isoWhiskerLeft R c.symm ≪≫
      (Functor.associator R D (SA ⋙ Re ⋙ Rv)).symm ≪≫
      Functor.isoWhiskerRight b (SA ⋙ Re ⋙ Rv) ≪≫
      Functor.associator E (Modules.restrictFunctor A.ι) (SA ⋙ Re ⋙ Rv) ≪≫
      Functor.isoWhiskerLeft E (
        (Functor.associator (Modules.restrictFunctor A.ι) SA (Re ⋙ Rv)).symm ≪≫
        Functor.isoWhiskerLeft (Modules.restrictFunctor A.ι ⋙ SA) r ≪≫
        (Functor.associator (Modules.restrictFunctor A.ι ⋙ SA) Ra Ru).symm ≪≫
        Functor.isoWhiskerRight ca Ru)
  refine ⟨V, hxV, hVU, a, k, ?_⟩
  have hac (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (t : ((D ⋙ SA ⋙ Re ⋙ Rv).obj (R.obj M))) :
      a.hom.app M (c.hom.app (R.obj M) t) =
        ca.hom.app (E.obj M) (SA.map (b.hom.app M) t) := by
    change ca.hom.app (E.obj M) (SA.map (b.hom.app M)
      (c.inv.app (R.obj M) (c.hom.app (R.obj M) t))) = _
    rw [show c.inv.app (R.obj M) (c.hom.app (R.obj M) t) = t from
      ConcreteCategory.congr_hom (c.hom_inv_id_app (R.obj M)) t]
  intro B hxB m
  let t : SA.obj ((Modules.restrictFunctor A.ι).obj (E.obj F)) :=
    ((Modules.restrictFunctor A.ι).obj (E.obj F)).presheaf.germ B y hxB m
  let w : (D ⋙ SA ⋙ Re ⋙ Rv).obj (R.obj F) := SA.map (b.inv.app F) t
  have ht : ca.hom.app (E.obj F) t =
      (E.obj F).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
        ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m :=
    ConcreteCategory.congr_hom
      (Modules.germ_restrictStalkNatIso_hom_app A.ι y (E.obj F) hxB) m
  have hw' : a.hom.app F (c.hom.app (R.obj F) w) =
      (E.obj F).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
        ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m := by
    rw [hac]
    change ca.hom.app (E.obj F) (SA.map (b.hom.app F) (SA.map (b.inv.app F) t)) = _
    rw [← ModuleCat.comp_apply, ← SA.map_comp, b.inv_hom_id_app,
      SA.map_id, ModuleCat.id_apply]
    exact ht
  have hw : a.inv.app F ((E.obj F).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
      ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m) = c.hom.app (R.obj F) w := by
    rw [← hw']
    exact ConcreteCategory.congr_hom (a.hom_inv_id_app F) _
  change a.hom.app N ((C ⋙ SV ⋙ Rv).map k
    (a.inv.app F ((E.obj F).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
      ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m))) =
    (E.obj N).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
      ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ (Modules.Hom.app f B m)
  rw [hw]
  have hc := (ConcreteCategory.congr_hom (c.hom.naturality k) w).symm
  change (C ⋙ SV ⋙ Rv).map k (c.hom.app (R.obj F) w) =
    c.hom.app (R.obj N) ((SA ⋙ Re ⋙ Rv).map (D.map k) w) at hc
  rw [hc, hac]
  change ca.hom.app (E.obj N) (SA.map (b.hom.app N) (SA.map (D.map k) w)) = _
  have hnk' : b.inv.app F ≫ D.map k ≫ b.hom.app N = f := by
    rw [hk]
    simp only [Category.assoc, b.inv_hom_id_app, b.inv_hom_id_app_assoc]
    exact Category.comp_id f
  have hnk : SA.map (b.hom.app N) (SA.map (D.map k) w) = SA.map f t := by
    change SA.map (b.hom.app N) (SA.map (D.map k) (SA.map (b.inv.app F) t)) = _
    simpa only [Functor.map_comp, ModuleCat.comp_apply] using!
      ConcreteCategory.congr_hom (congrArg SA.map hnk') t
  have hn := congrArg (fun z ↦ ca.hom.app (E.obj N) z) hnk
  apply hn.trans
  have htf : SA.map f t =
      ((Modules.restrictFunctor A.ι).obj (E.obj N)).presheaf.germ B y hxB
        (Modules.Hom.app f B m) := by
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply B y hxB
      (Modules.Hom.mapPresheaf f) m
  exact (congrArg (fun z ↦ ca.hom.app (E.obj N) z) htf).trans
    (ConcreteCategory.congr_hom
      (Modules.germ_restrictStalkNatIso_hom_app A.ι y (E.obj N) hxB)
      (Modules.Hom.app f B m))



/-- Transport an already constructed local morphism from the open subscheme to the slice site.

Source: Stacks Project, Sheaves Tag 00A0 (3), restriction to an open subspace.
(blueprint: new-lem-sc-open-stalk-unit-map-one-lift-bridge).

Proof: Put V = U.ι ''ᵁ A, so x belongs to V and V is contained in U. The open subscheme
V is canonically isomorphic to A.toScheme over U.toScheme. Restrict f along this isomorphism.
The natural isomorphism Modules.overMapCompOverEquiv identifies its source and target with
those of the images of the slice restrictions of F and N under Modules.overEquiv V.
Conjugate by these components and take the preimage under this fully faithful equivalence
to obtain k. Use the canonical restriction-stalk comparison, constructed from the same-germ
formula, for a. Every stalk element on V is represented by a section on a neighbourhood of
x; transfer that section to A and apply hf. The germ formulas for restriction and the
slice equivalence give S.map k followed by a_N = a_F followed by the scalar restriction
of q. Linearity holds because the composite of the two open-immersion stalk ring maps is
U.ι.stalkMap. Compose with a_N inverse to get the displayed equation. No local existence
of f is proved here; f and its germ equation are inputs, for arbitrary F and N. -/
theorem exists_open_stalk_hom_of_subscheme_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (F N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (q : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨x, hxU⟩).obj
        ((Modules.overEquiv U).functor.obj F) ⟶
      (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨x, hxU⟩).obj
        ((Modules.overEquiv U).functor.obj N))
    (A : U.toScheme.Opens) (hxA : (⟨x, hxU⟩ : U.toScheme) ∈ A)
    (f : (Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj F) ⟶
      (Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj N))
    (hf : ∀ (B : A.toScheme.Opens)
      (hxB : (⟨⟨x, hxU⟩, hxA⟩ : A.toScheme) ∈ B)
      (m : Γ((Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj F), B)),
      ((Modules.overEquiv U).functor.obj N).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
          ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ (Modules.Hom.app f B m) =
        q (((Modules.overEquiv U).functor.obj F).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
          ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
      let S := openModuleStalkFunctor X V ⟨x, hxV⟩
      ∃ (a : R ⋙ S ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (k : R.obj F ⟶ R.obj N),
        S.map k = a.hom.app F ≫
          (ModuleCat.restrictScalars (U.ι.stalkMap ⟨x, hxU⟩).hom).map q ≫
            a.inv.app N := by
  obtain ⟨V, hxV, hVU, a, k, hk⟩ :=
    exists_slice_hom_with_subscheme_germ_formula X U x hxU F N A hxA f
  refine ⟨V, hxV, hVU, a, k, ?_⟩
  apply (cancel_mono (a.hom.app N)).mp
  simp only [Category.assoc, a.inv_hom_id_app]
  ext m
  let M := (Modules.overEquiv U).functor.obj F
  let c := (Modules.restrictStalkNatIso A.ι ⟨⟨x, hxU⟩, hxA⟩).app M
  obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso c.hom).2 (a.hom.app F m)
  obtain ⟨B, hxB, s, hs⟩ :=
    ((Modules.restrictFunctor A.ι).obj M).presheaf.exists_germ_eq t
  have hg : M.presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
      ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ s = a.hom.app F m := by
    rw [← ht, ← hs]
    exact (ConcreteCategory.congr_hom
      (Modules.germ_restrictStalkNatIso_hom_app A.ι ⟨⟨x, hxU⟩, hxA⟩ M hxB) s).symm
  have hi : a.inv.app F (a.hom.app F m) = m :=
    ConcreteCategory.congr_hom (a.hom_inv_id_app F) m
  have hkm := hk B hxB s
  rw [hg, hi] at hkm
  change a.hom.app N ((openModuleStalkFunctor X V ⟨x, hxV⟩).map k m) =
    q (a.hom.app F m)
  rw [hkm, hf B hxB s, hg]

end
end AlgebraicGeometry.Scheme
