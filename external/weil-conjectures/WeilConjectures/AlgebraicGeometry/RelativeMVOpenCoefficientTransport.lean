/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenIso
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenUnit
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionUnitIso

/-! # Coefficient comparison for an inverse-image open

Source: Stacks Project, Cohomology, Tags 08HY and 0D5S.
(blueprint: lem-pc-relative-mv-open-coefficient-transport).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable [d : ∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem iso_open_transport_unit {A B X : Scheme.{u}} (s : B ≅ A)
    (j : A ⟶ X) (p : B ⟶ X) (h : s.hom ≫ j = p)
    (K : schemeDerivedCategory X) :
    (relativeMVAdj j).unit.app K ≫ (relativeMVIsoOpenTransport s j p h K).hom =
      (relativeMVAdj p).unit.app K := by
  let c := relativeMVComp s.hom j ≪≫
    eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  let a := ((relativeMVAdj j).comp (relativeMVAdj s.hom)).ofNatIsoLeft c
  have hu := Adjunction.unit_rightAdjointUniq_hom_app a (relativeMVAdj p) K
  simpa only [a, c, relativeMVIsoOpenTransport, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.app_hom, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] using hu


private theorem inverse_open_localization_unit {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (W : X.Opens) (K' : schemeDerivedCategory X') :
    (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).unit.app K' ≫
      (relativeMVInverseOpenLocalizationIso g' W K').hom =
      (relativeMVAdj (pullback.fst g' W.ι)).unit.app K' := by
  simp only [relativeMVInverseOpenLocalizationIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, ← Category.assoc]
  rw [Adjunction.unit_leftAdjointUniq_hom_app, iso_open_transport_unit]


omit d in
private theorem precomp_injective_of_restriction_isIso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B : C} (i : A ⟶ B) [IsIso (L.map i)]
    {Z : D} {p q : B ⟶ R.obj Z} (h : i ≫ p = i ≫ q) : p = q := by
  apply (a.homEquiv _ _).symm.injective
  apply (cancel_epi (L.map i)).mp
  simpa only [← a.homEquiv_naturality_left_symm] using
    congrArg (a.homEquiv _ _).symm h


omit d in
private theorem mate_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (P : C ⥤ C') (Q : D ⥤ D')
    (e : P ⋙ L' ≅ L ⋙ Q) (K : C) (K' : C') (ψ : P.obj K ⟶ K') :
    P.map (a.unit.app K) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj (L.obj K)) ≫
          Q.map (a.counit.app (L.obj K))) ≫
        R'.map (e.inv.app K ≫ L'.map ψ) = ψ ≫ a'.unit.app K' := by
  rw [← a'.homEquiv_naturality_right, ← a'.homEquiv_naturality_left]
  have ht :
      L'.map (P.map (a.unit.app K)) ≫
          (e.hom.app (R.obj (L.obj K)) ≫ Q.map (a.counit.app (L.obj K))) ≫
          (e.inv.app K ≫ L'.map ψ) = L'.map ψ := by
    simp only [← Category.assoc]
    have hn := e.hom.naturality (a.unit.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    simp only [Category.assoc, ← Q.map_comp_assoc, a.left_triangle_components,
      Functor.id_obj, Functor.comp_obj,
      Q.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [ht, Adjunction.homEquiv_unit, a'.unit_naturality]


/-- The open-square mate respects the exact-to-pinned coefficient comparisons.
This is an identity on X', before any further direct image to a base scheme.
Source: Stacks Project, Cohomology, Remark 08HY and Lemma 08HZ;
Schemes, Tag 01JR.
(blueprint: lem-pc-relative-mv-open-coefficient-transport).

Proof: Precompose both sides with Lg' of the exact-open unit. This
precomposition is injective on maps into Rp: exact restriction to the inverse
open inverts Lg' of the unit, by the pullback/restriction comparison and the
open-unit invertibility theorem; Lp is this exact restriction followed by
pullback along the inverse-open isomorphism, up to the specified comparison.
For the left side, the proved exact-open base-change unit identity leaves φ
followed by the inverse-open unit. The localization comparison preserves
that unit, by left- and right-adjoint uniqueness. For the right side,
left-adjoint uniqueness replaces the exact-open unit by the pinned unit.
Transposing the open-square mate cancels this unit with the pulled-back
counit; naturality of the square comparison and the triangle identity leave
φ followed by the p unit. Thus the precomposites coincide, and injectivity
gives the result. Empty and full opens and zero objects or maps need no
additional assumption: the same adjunction identities and invertibility
apply in all these cases. -/
theorem relativeMV_open_coefficient_transport
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) :
    schemeDerivedBaseChangeMap W.ι (g' ⁻¹ᵁ W).ι g'
        (g'.resLE W (g' ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl)
        ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
      (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).map
        ((mvPullbackOpenRestrictionIso g' W).inv.app K ≫
          (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map φ) ≫
      (relativeMVInverseOpenLocalizationIso g' W K').hom =
    (derivedPullback g').map ((schemeDerivedDirectImage W.ι).map
        (((mvOpenRestrictionAdjunction X W).leftAdjointUniq
          (relativeMVAdj W.ι)).hom.app K)) ≫
      schemeDerivedBaseChangeMap W.ι (pullback.fst g' W.ι) g'
        (pullback.snd g' W.ι) (pullback.condition (f := g') (g := W.ι)).symm
        ((derivedPullback W.ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' W.ι)).map
        ((relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app K ≫
          eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
            (pullback.condition (f := g') (g := W.ι)).symm) ≫
          (relativeMVComp (pullback.fst g' W.ι) g').inv.app K ≫
          (derivedPullback (pullback.fst g' W.ι)).map φ) := by
  let u := (mvOpenRestrictionAdjunction X W).unit.app K
  let p := pullback.fst g' W.ι
  let v := pullback.snd g' W.ι
  let e := relativeMVComp p g' ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (pullback.condition (f := g') (g := W.ι))) ≪≫
    (relativeMVComp v W.ι).symm
  have : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map u) :=
    schemeDerivedOpen_unit_isIso X W (mvOpenRestrictionAdjunction X W) K
  have : IsIso (((schemeOpenRestriction X W).mapDerivedCategory ⋙
      derivedPullback (g'.resLE W (g' ⁻¹ᵁ W) le_rfl)).map u) := by
    change IsIso ((derivedPullback _).map
      ((schemeOpenRestriction X W).mapDerivedCategory.map u))
    infer_instance
  have : IsIso (((derivedPullback g') ⋙
      (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory).map u) :=
    (NatIso.isIso_map_iff (mvPullbackOpenRestrictionIso g' W) u).mpr inferInstance
  let s := pullbackRestrictIsoRestrict g' W
  let c : (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory ⋙
      derivedPullback s.hom ≅ derivedPullback p :=
    Functor.isoWhiskerRight
        ((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).leftAdjointUniq
          (relativeMVAdj (g' ⁻¹ᵁ W).ι)) (derivedPullback s.hom) ≪≫
      relativeMVComp s.hom (g' ⁻¹ᵁ W).ι ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k)
        (pullbackRestrictIsoRestrict_hom_ι g' W))
  have : IsIso ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map
      ((derivedPullback g').map u)) := by
    change IsIso (((derivedPullback g') ⋙
      (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory).map u)
    infer_instance
  have : IsIso (((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory ⋙
      derivedPullback s.hom).map ((derivedPullback g').map u)) := by
    change IsIso ((derivedPullback s.hom).map
      ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map
        ((derivedPullback g').map u)))
    infer_instance
  have : IsIso ((derivedPullback p).map ((derivedPullback g').map u)) :=
    (NatIso.isIso_map_iff c ((derivedPullback g').map u)).mp inferInstance
  apply precomp_injective_of_restriction_isIso (relativeMVAdj p)
    ((derivedPullback g').map u)
  have hl := mvOpenBaseChange_unit g' K K' φ W
  have hr := mate_unit (relativeMVAdj W.ι) (relativeMVAdj p)
    (derivedPullback g') (derivedPullback v) e K K' φ
  have hleft : (derivedPullback g').map u ≫
      (schemeDerivedBaseChangeMap W.ι (g' ⁻¹ᵁ W).ι g'
        (g'.resLE W (g' ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl)
        ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
      (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).map
        ((mvPullbackOpenRestrictionIso g' W).inv.app K ≫
          (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map φ) ≫
      (relativeMVInverseOpenLocalizationIso g' W K').hom) =
      φ ≫ (relativeMVAdj p).unit.app K' := by
    have h := congrArg (fun t ↦ t ≫
      (relativeMVInverseOpenLocalizationIso g' W K').hom) hl
    simpa only [u, p, Category.assoc, inverse_open_localization_unit] using h
  rw [hleft]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [Adjunction.unit_leftAdjointUniq_hom_app]
  symm
  simpa only [e, p, v, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    Category.assoc, Functor.id_obj, Functor.comp_obj, schemeDerivedBaseChangeMap,
    relativeMVAdj, relativeMVComp] using hr

end AlgebraicGeometry
