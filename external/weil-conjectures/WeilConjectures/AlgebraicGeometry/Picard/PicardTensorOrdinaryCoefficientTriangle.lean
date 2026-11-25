/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueNormalizationMap

/-! # PicardTensorOrdinaryCoefficientTriangle

## References

* Stacks Project, Tags 0096, 06YJ, 0A1D, 08HY, 0D5S and 01F7
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem uniq
    {A B : Type*} [Category A] [Category B] {F F' : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Equiv.apply_symm_apply]

private theorem compat
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Tf Pf : B ⥤ C} {Tg Pg : A ⥤ B} {Tfg Pfg : A ⥤ C}
    {Rf : C ⥤ B} {Rg : B ⥤ A} {Rfg : C ⥤ A}
    (af : Tf ⊣ Rf) (bf : Pf ⊣ Rf) (ag : Tg ⊣ Rg) (bg : Pg ⊣ Rg)
    (afg : Tfg ⊣ Rfg) (bfg : Pfg ⊣ Rfg)
    (p : Pg ⋙ Pf ≅ Pfg) (q : Rf ⋙ Rg ≅ Rfg)
    (hp : conjugateEquiv (bg.comp bf) bfg p.inv = q.hom) :
    Functor.whiskerRight (ag.leftAdjointUniq bg).hom Tf ≫
      Functor.whiskerLeft Pg (af.leftAdjointUniq bf).hom ≫ p.hom =
      ((conjugateIsoEquiv afg (ag.comp af)).symm q.symm).hom ≫
        (afg.leftAdjointUniq bfg).hom := by
  have hp' : conjugateEquiv bfg (bg.comp bf) p.hom = q.inv := by
    have h := conjugateEquiv_comm (bg.comp bf) bfg p.hom_inv_id
    rw [hp] at h
    simpa using (Iso.eq_inv_comp q).2 h
  apply (conjugateEquiv bfg (ag.comp af)).injective
  rw [← conjugateEquiv_comp bfg (bg.comp af) (ag.comp af)
    (Functor.whiskerLeft Pg (af.leftAdjointUniq bf).hom ≫ p.hom)
    (Functor.whiskerRight (ag.leftAdjointUniq bg).hom Tf)]
  rw [← conjugateEquiv_comp bfg (bg.comp bf) (bg.comp af)
    p.hom (Functor.whiskerLeft Pg (af.leftAdjointUniq bf).hom)]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft]
  simp only [uniq, hp']
  simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id]
  rw [← conjugateEquiv_comp bfg afg (ag.comp af)]
  simp only [uniq, Category.id_comp, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply, Iso.symm_hom]

private theorem mixed
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {T P : B ⥤ C} {H : A ⥤ C}
    {R : B ⥤ A} {S : C ⥤ B} {U : C ⥤ A}
    (a : F ⊣ R) (b : T ⊣ S) (b' : P ⊣ S) (c : H ⊣ U)
    (e : S ⋙ R ≅ U) :
    Functor.whiskerLeft F (b.leftAdjointUniq b').inv ≫
      ((conjugateIsoEquiv (a.comp b) c).symm e).inv =
      (Adjunction.leftAdjointCompIso a b' c e).hom := by
  apply (conjugateEquiv c (a.comp b')).injective
  rw [← conjugateEquiv_comp c (a.comp b) (a.comp b')]
  rw [conjugateEquiv_whiskerLeft]
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointCompIso,
    conjugateIsoEquiv_symm_apply_inv, conjugateIsoEquiv_symm_apply_hom]

/-- The tensor mate and the ordinary pullback triangle define the same map. -/
theorem picard_tensor_ordinary_coefficient_triangle
    {A B X : Scheme.{v}} (q : A ⟶ X) (q' : B ⟶ X) (b : B ⟶ A)
    (hb : b ≫ q = q') (L : X.Modules) :
    Modules.tensorCoefficientComparison q q' b hb L =
      picardOrdinaryCoefficientTriangle q q' b hb L := by
  classical
  subst q'
  let aTensor := Modules.coefficientTensorAdjunction q
  let ap := Modules.pullbackPushforwardAdjunction q
  let ab := Modules.pullbackPushforwardAdjunction b
  let bt := Modules.coefficientTensorAdjunction b
  let ct := Modules.coefficientTensorAdjunction (b ≫ q)
  let cp := Modules.pullbackPushforwardAdjunction (b ≫ q)
  let e := Modules.pushforwardComp b q
  have h := compat ab ab aTensor ap ct cp (Modules.pullbackComp b q) e
    (Modules.conjugateEquiv_pullbackComp_inv b q)
  have hh := congrArg (fun z ↦ z.app L) h
  have hm := mixed aTensor bt ab ct e
  have hm' := congrArg (fun z ↦ z.app L) hm
  have he0 : Modules.pushforwardCongr (rfl : (b ≫ q) = (b ≫ q)) = Iso.refl _ := by
    ext N U
    simp
  have hc : (Modules.tensorCoefficientComparison q (b ≫ q) b rfl L).hom =
      (Adjunction.leftAdjointCompIso aTensor ab ct e).hom.app L := by
    rw [Modules.tensorCoefficientComparison_eq, he0]
    simpa only [aTensor, bt, ab, ct, e, Modules.coefficientTensorAdjunction,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_refl] using hm'
  have h' : (Modules.pullback b).map ((aTensor.leftAdjointUniq ap).hom.app L) ≫
      (Modules.pullbackComp b q).hom.app L =
      (Adjunction.leftAdjointCompIso aTensor ab ct e).hom.app L ≫
        (ct.leftAdjointUniq cp).hom.app L := by
    simpa only [Adjunction.leftAdjointUniq_refl, Functor.whiskerLeft_id',
      NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Adjunction.leftAdjointCompIso,
      Iso.symm_hom, Iso.symm_inv] using hh
  apply Iso.ext
  rw [hc]
  apply (cancel_mono ((ct.leftAdjointUniq cp).hom.app L)).mp
  simpa only [aTensor, ap, ct, cp, Modules.coefficientTensorAdjunction,
    picardOrdinaryCoefficientTriangle, Iso.trans_hom, Iso.app_inv,
    Functor.mapIso_hom, Iso.app_hom, Modules.pullbackCongr, Iso.trans_refl,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h'.symm

end AlgebraicGeometry.Scheme
