/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps

/-! # Open component compatibility for derived base change

Source: Stacks Project, Tags 08HY, 08BV and 0DJ9.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AlgebraicGeometry

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

private theorem mate_unit_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L A : C ⥤ D} {R : D ⥤ C} {L' A' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (ar : A ⊣ R) (a' : L' ⊣ R') (ar' : A' ⊣ R')
    (P : C ⥤ C') (Q : D ⥤ D') (e : P ⋙ L' ≅ L ⋙ Q)
    (K : C) (K' : C') (ψ : P.obj K ⟶ K') :
    let b := Functor.isoWhiskerLeft P (a'.leftAdjointUniq ar').symm ≪≫ e ≪≫
      Functor.isoWhiskerRight (a.leftAdjointUniq ar) Q
    P.map (ar.unit.app K) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj (A.obj K)) ≫
          Q.map (a.counit.app (A.obj K))) ≫
        R'.map (b.inv.app K ≫ A'.map ψ) = ψ ≫ ar'.unit.app K' := by
  intro b
  let d := a.leftAdjointUniq ar
  let d' := a'.leftAdjointUniq ar'
  have hc : Q.map (d.hom.app K) ≫ b.inv.app K =
      e.inv.app K ≫ d'.hom.app (P.obj K) := by
    simp only [b, d, d', Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      ← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id, Category.id_comp]
  rw [← Adjunction.unit_leftAdjointUniq_hom_app a ar K]
  simp only [P.map_comp, Category.assoc, Functor.comp_obj, Functor.id_obj]
  have hm : P.map (R.map ((a.leftAdjointUniq ar).hom.app K)) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj (A.obj K)) ≫ Q.map (a.counit.app (A.obj K))) =
      a'.homEquiv _ _ (e.hom.app (R.obj (L.obj K)) ≫ Q.map (a.counit.app (L.obj K))) ≫
        R'.map (Q.map ((a.leftAdjointUniq ar).hom.app K)) := by
    simpa [Adjunction.homEquiv_unit, mateEquiv] using
      (mateEquiv a a' e.hom).naturality ((a.leftAdjointUniq ar).hom.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hm
  rw [← Category.assoc (P.map (R.map ((a.leftAdjointUniq ar).hom.app K))), hm]
  simp only [Category.assoc, ← R'.map_comp]
  have hn := d'.hom.naturality ψ
  change P.map (a.unit.app K) ≫
      a'.homEquiv _ _ (e.hom.app (R.obj (L.obj K)) ≫
        Q.map (a.counit.app (L.obj K))) ≫
      R'.map (Q.map (d.hom.app K) ≫ b.inv.app K ≫ A'.map ψ) = _
  rw [← Category.assoc (Q.map (d.hom.app K)), hc, Category.assoc, ← hn]
  simp only [R'.map_comp, ← Category.assoc, Functor.comp_obj, Functor.id_obj]
  have hm := mate_unit a a' P Q e K K' ψ
  simp only [Functor.comp_obj, Functor.id_obj, R'.map_comp, ← Category.assoc] at hm
  rw [hm]
  rw [Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app a' ar' K']

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The canonical open base-change mate commutes with the exact-open unit.
Source: Stacks Project, Cohomology, Remark 08HY and Lemma 08BV.
(blueprint: lem-pc-rf-mv-open-base-change-unit).
Proof: For e:P;L′≅L;Q and adjunctions L⊣R, L′⊣R′, write its mate as
β_Y=homEquiv′(e_RY;Q(ε_Y)). Naturality gives P(R(k));β=β;R′(Q(k)).
Transpose P(η_K);β_LK;R′(e_K inverse;L′(ψ)). Naturality of e and the triangle
identity cancel the middle unit and counit, then e and its inverse cancel.
The remaining transpose is L′(ψ), whose mate is ψ;η′. To pass to exact-open
restriction, use d=leftAdjointUniq and d′=leftAdjointUniq: their unit equations
replace η by η;R(d). Move d through β by mate naturality; in the inverse of
b=P(d′ inverse);e;Q(d), d cancels with d inverse. Naturality of d′ and its
unit equation give the exact-open target unit. For opens, e is precisely the
composite of the two pinned pullback composition comparisons and the equality
of restricted morphisms; b is the defined mvPullbackOpenRestrictionIso.
No coherence for triple compositions or geometric finiteness is needed. -/
theorem mvOpenBaseChange_unit
    {X X' : Scheme.{u}} (q : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback q).obj K ⟶ K') (U : X.Opens) :
    (derivedPullback q).map ((mvOpenRestrictionAdjunction X U).unit.app K) ≫
        schemeDerivedBaseChangeMap U.ι (q ⁻¹ᵁ U).ι q
          (q.resLE U (q ⁻¹ᵁ U) le_rfl) (Scheme.Hom.resLE_comp_ι q le_rfl)
          ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ≫
        (schemeDerivedDirectImage (q ⁻¹ᵁ U).ι).map
          ((mvPullbackOpenRestrictionIso q U).inv.app K ≫
            (schemeOpenRestriction X' (q ⁻¹ᵁ U)).mapDerivedCategory.map ψ) =
      ψ ≫ (mvOpenRestrictionAdjunction X' (q ⁻¹ᵁ U)).unit.app K' := by
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) a b
  let e := c (q ⁻¹ᵁ U).ι q ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (Scheme.Hom.resLE_comp_ι q (U := U) le_rfl).symm) ≪≫
      (c (q.resLE U (q ⁻¹ᵁ U) le_rfl) U.ι).symm
  have hu := mate_unit_transport (mvDerivedPullbackAdjunction U.ι)
    (mvOpenRestrictionAdjunction X U)
    (mvDerivedPullbackAdjunction (q ⁻¹ᵁ U).ι)
    (mvOpenRestrictionAdjunction X' (q ⁻¹ᵁ U))
    (derivedPullback q) (derivedPullback (q.resLE U (q ⁻¹ᵁ U) le_rfl)) e K K' ψ
  let b := Functor.isoWhiskerLeft (derivedPullback q)
      (mvOpenPullbackIso X' (q ⁻¹ᵁ U)).symm ≪≫ e ≪≫
    Functor.isoWhiskerRight (mvOpenPullbackIso X U)
      (derivedPullback (q.resLE U (q ⁻¹ᵁ U) le_rfl))
  have hb : mvPullbackOpenRestrictionIso q U = b := by
    simp only [mvPullbackOpenRestrictionIso, b, e, c, Iso.trans_assoc]
  rw [hb]
  change (derivedPullback q).map ((mvOpenRestrictionAdjunction X U).unit.app K) ≫
      (mvDerivedPullbackAdjunction (q ⁻¹ᵁ U).ι).homEquiv _ _
        ((c (q ⁻¹ᵁ U).ι q).hom.app
            ((schemeDerivedDirectImage U.ι).obj
              ((schemeOpenRestriction X U).mapDerivedCategory.obj K)) ≫
          eqToHom (congrArg (fun t ↦ (derivedPullback t).obj
            ((schemeDerivedDirectImage U.ι).obj
              ((schemeOpenRestriction X U).mapDerivedCategory.obj K)))
            (Scheme.Hom.resLE_comp_ι q (U := U) le_rfl).symm) ≫
          (c (q.resLE U (q ⁻¹ᵁ U) le_rfl) U.ι).inv.app
            ((schemeDerivedDirectImage U.ι).obj
              ((schemeOpenRestriction X U).mapDerivedCategory.obj K)) ≫
          (derivedPullback (q.resLE U (q ⁻¹ᵁ U) le_rfl)).map
            ((mvDerivedPullbackAdjunction U.ι).counit.app
              ((schemeOpenRestriction X U).mapDerivedCategory.obj K))) ≫
      (schemeDerivedDirectImage (q ⁻¹ᵁ U).ι).map
        (b.inv.app K ≫ (schemeOpenRestriction X' (q ⁻¹ᵁ U)).mapDerivedCategory.map ψ) = _
  simpa only [b, mvOpenPullbackIso, e, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_obj, Functor.id_obj,
    Category.assoc] using hu


end AlgebraicGeometry
