/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Bijectivity of the regular-module stalk comparison

Source: Stacks Project, Tags 01HV, 01IB and 0098.
(blueprint: lem-sc-affine-regular-stalk-comparison-bijective).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme

-- Germ representatives and equality witnesses may be chosen inside the fixed open U.
set_option backward.isDefEq.respectTransparency false in
private theorem stalk_map_bijective (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hxU : x ∈ U) (F G : X.carrier.Presheaf Ab.{u}) (f : F ⟶ G)
    (hf : ∀ V : X.Opens, V ≤ U → Function.Bijective (f.app (.op V))) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f) := by
  constructor
  · intro s t hst
    obtain ⟨V, hVU, hxV, s, rfl⟩ := F.exists_le_germ_eq s hxU
    obtain ⟨W, hWU, hxW, t, rfl⟩ := F.exists_le_germ_eq t hxU
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨Z, hxZ, iV, iW, he⟩ := G.germ_eq x hxV hxW _ _ hst
    have hnV := ConcreteCategory.congr_hom (f.naturality iV.op) s
    have hnW := ConcreteCategory.congr_hom (f.naturality iW.op) t
    simp only [ConcreteCategory.comp_apply] at hnV hnW
    have he' : F.map iV.op s = F.map iW.op t :=
      (hf Z (iV.le.trans hVU)).1 (hnV.trans (he.trans hnW.symm))
    rw [← F.germ_res_apply iV x hxZ s, ← F.germ_res_apply iW x hxZ t, he']
  · intro t
    obtain ⟨V, hVU, hxV, t, rfl⟩ := G.exists_le_germ_eq t hxU
    obtain ⟨s, hs⟩ := (hf V hVU).2 t
    refine ⟨F.germ V x hxV s, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs]

-- Reuse the proved private calculation in IdealModuleProductStalk without importing
-- that module's unrelated ideal-product theory.
set_option backward.isDefEq.respectTransparency false in
private theorem unit_stalk_iso (X : Scheme.{u}) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
  let D := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}
  let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
    (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
      e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r := by
    change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : OpenNhds x)) ≫
      (preservesColimitIso A D).inv) r = _
    rw [ι_preservesColimitIso_inv]
    rfl
  let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
          ← TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            (homOfLE inf_le_right) x hx m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
        let m' : Γ(X, U ⊓ V) :=
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
            (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
        change e (TopCat.Presheaf.germ
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
          X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
              X.presheaf.stalk x)
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
  refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
  exact hg

/-- The unit germ identifies the ambient stalk ring with the stalk of the sheafification
of the regular coordinate module, after ordinary open direct image.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4 (6)-(7), and Tags 01IB and 0098.
(blueprint: lem-sc-affine-regular-stalk-comparison-bijective).

Proof: The explicit affineRegularSheafIso identifies the sheafification of the regular
module with the structure sheaf on the slice site. Each factor (tildeSelf,
restrictUnitIso, and the unit isomorphism of overEquiv) takes its unit to the unit
section. For any neighbourhood V contained in U, ordinary direct image of that
structure sheaf has sections O_X(V), with the same restrictions and scalar actions:
the slice object V times U is identified with V by the second projection because
V is contained in U. These neighbourhoods are cofinal at x. Taking their colimit
therefore identifies its stalk with O_{X,x}, taking the unit germ to 1. Multiplication
by the unit germ consequently identifies r with r in this colimit, and is bijective.
Composing with the direct image and stalk of affineRegularSheafIso gives precisely
affineRegularStalkComparison. No quasi-compactness hypothesis is used; an empty U
admits no x with hxU. -/
theorem affineRegularStalkComparison_bijective
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U) :
    Function.Bijective (affineRegularStalkComparison X x U hxU hU)  := by
  let R := moduleRings X.toRingedSpace
  let P := SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := R) U)
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let f := SheafOfModules.unitToPushforwardObjUnit
    (SheafOfModules.pushforwardOver (R := R) U)
  have hf : Function.Bijective (S.map f) := by
    apply stalk_map_bijective X x U hxU
    intro V hVU
    change Function.Bijective (R.obj.map
      (Limits.prod.snd : Limits.prod U V ⟶ V).op)
    have : IsIso (Limits.prod.snd : Limits.prod U V ⟶ V) := by
      refine ⟨⟨Limits.prod.lift (homOfLE hVU) (𝟙 V), ?_, ?_⟩⟩
      · exact Subsingleton.elim _ _
      · exact Subsingleton.elim _ _
    exact ConcreteCategory.bijective_of_isIso _
  obtain ⟨eu, heu⟩ := unit_stalk_iso X x
  let e := (P ⋙ S).mapIso (affineRegularSheafIso X U hU)
  let g := TopCat.Presheaf.germ (P.obj (SheafOfModules.unit (R.over U))).val.presheaf
    U x hxU (1 : (R.over U).obj.obj (.op ((Over.star U).obj U)))
  have he : e.hom (affineRegularStalkGerm X x U hxU hU) = g := by
    have hginv : e.inv g = affineRegularStalkGerm X x U hxU hU := by
      change RingedSpace.stalkAddMap X.toRingedSpace x
        (P.map (affineRegularSheafIso X U hU).inv) g = _
      dsimp only [RingedSpace.stalkAddMap, g]
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rfl
    rw [← hginv]
    exact e.inv_hom_id_apply g
  have hfg : (S.map f) (eu.inv 1) = g := by
    have hunit := heu U hxU 1
    have hunit' : eu.inv 1 = TopCat.Presheaf.germ
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf U x hxU (1 : Γ(X, U)) := by
      apply (ConcreteCategory.bijective_of_isIso eu.hom).1
      simpa using hunit.symm
    rw [hunit']
    change RingedSpace.stalkAddMap X.toRingedSpace x f _ = _
    dsimp only [RingedSpace.stalkAddMap]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ
      (P.obj (SheafOfModules.unit (R.over U))).val.presheaf U x hxU
      ((R.obj.map (Limits.prod.snd : Limits.prod U U ⟶ U).op) 1) = g
    rw [map_one]
  have hc (r : X.presheaf.stalk x) :
      e.hom (affineRegularStalkComparison X x U hxU hU r) =
        (S.map f) (eu.inv r) := by
    change e.hom (r • affineRegularStalkGerm X x U hxU hU) = _
    rw [map_smul, he]
    have hr : eu.inv r = r • eu.inv 1 := by
      rw [← map_smul]
      congr 1
      exact (mul_one r).symm
    rw [hr, map_smul, hfg]
  have hb : Function.Bijective (fun r ↦
      e.hom (affineRegularStalkComparison X x U hxU hU r)) := by
    simp_rw [hc]
    exact hf.comp (ConcreteCategory.bijective_of_isIso eu.inv)
  exact (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso e.hom) _).mp hb

end AlgebraicGeometry.Scheme
