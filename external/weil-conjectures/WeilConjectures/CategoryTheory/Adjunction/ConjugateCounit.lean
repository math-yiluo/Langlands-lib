/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Counits of conjugated composition isomorphisms

Let `L_F ⊣ R_F`, `L_h ⊣ R_h` and `G ⊣ R_G` be adjunctions, `c : L_F ≅ L_h ⋙ G` a composition
isomorphism of left adjoints and `ι : G ≅ 𝟭` an identity isomorphism. Their conjugates are a
composition isomorphism `R_F ≅ R_G ⋙ R_h` and an identity isomorphism `R_G ≅ 𝟭` of the right
adjoints. This file records how the counits interact with these conjugates; it is used for the
exceptional functors of the six-functor formalism, where `c` and `ι` are the composition and
identity isomorphisms of the lower shriek and their conjugates those of the upper shriek.

## Main results

- `CategoryTheory.conjugateIsoEquiv_comp_unit_counit`: if `c` composed with `ι` is an
  isomorphism `e : L_F ≅ L_h`, then the counit of `L_h ⊣ R_h`, composed with the conjugates of
  `c` and `ι`, is the counit of `L_F ⊣ R_F` transported along `e`.
- `CategoryTheory.Adjunction.counit_eqToHom_family`: transport of counits along an equality of
  indices in a family of adjunctions.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Let `c : L_F ≅ L_h ⋙ G` and `ι : G ≅ 𝟭` be isomorphisms of left adjoints whose composite is
`e : L_F ≅ L_h`. Then, for the conjugates `R_F ≅ R_G ⋙ R_h` of `c` and `R_G ≅ 𝟭` of `ι`, the
composite `L_h R_F K ⟶ L_h R_h R_G K ⟶ R_G K ⟶ K` of the conjugate of `c`, the counit of
`L_h ⊣ R_h` and the conjugate of `ι` is `L_h R_F K ≅ L_F R_F K ⟶ K`. -/
lemma conjugateIsoEquiv_comp_unit_counit {LF Lh : C ⥤ D} {RF Rh : D ⥤ C} {G RG : D ⥤ D}
    (adjF : LF ⊣ RF) (adjh : Lh ⊣ Rh) (adjG : G ⊣ RG) (c : LF ≅ Lh ⋙ G) (ι : G ≅ 𝟭 D)
    (e : LF ≅ Lh) (hc : ∀ K, c.hom.app K ≫ ι.hom.app (Lh.obj K) = e.hom.app K) (K' : D) :
    Lh.map ((conjugateIsoEquiv adjF (adjh.comp adjG) c.symm).hom.app K') ≫
        adjh.counit.app (RG.obj K') ≫
        (conjugateIsoEquiv adjG Adjunction.id ι.symm).hom.app K' =
      e.inv.app (RF.obj K') ≫ adjF.counit.app K' := by
  have hι := conjugateEquiv_counit adjG Adjunction.id ι.inv K'
  have hC := conjugateEquiv_counit adjF (adjh.comp adjG) c.inv K'
  have he : ι.inv.app (Lh.obj (RF.obj K')) ≫ c.inv.app (RF.obj K') = e.inv.app (RF.obj K') := by
    rw [← cancel_mono (e.hom.app _), Category.assoc, Iso.inv_hom_id_app, ← hc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rfl
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Adjunction.id_counit,
    NatTrans.id_app, Category.comp_id] at hι
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at hC
  rw [conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_hom, Iso.symm_hom, Iso.symm_hom, hι,
    ← he, Category.assoc, ← hC]
  have h1 := ι.inv.naturality (adjh.counit.app (RG.obj K'))
  have h2 := ι.inv.naturality (Lh.map ((conjugateEquiv adjF (adjh.comp adjG) c.inv).app K'))
  simp only [Functor.id_obj, Functor.id_map] at h1 h2
  rw [reassoc_of% h1, reassoc_of% h2]

/-- Transport of counits along an equality `m = m'` of indices in a family of adjunctions
`L m ⊣ R m`. -/
lemma Adjunction.counit_eqToHom_family {M : Type*} (L : M → C ⥤ D) (R : M → D ⥤ C)
    (adj : ∀ m, L m ⊣ R m) {m m' : M} (hm : m = m') (K : D) :
    (L m').map (eqToHom (congrArg (fun n ↦ (R n).obj K) hm.symm)) ≫
        eqToHom (congrArg (fun n ↦ (L n).obj ((R m).obj K)) hm.symm) ≫ (adj m).counit.app K =
      (adj m').counit.app K := by
  subst hm
  simp

end CategoryTheory

namespace CategoryTheory

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]

/-- **Functoriality of pushforwards of sections**, abstractly. Let `f^* ⊣ f_*`, `f_! ⊣ f^!`
(and the same for `g` and `F = f ≫ g`) be adjunctions with identifications `f_! ≅ f_*`, units
`ε_f : 𝟙₁ ≅ f^* 𝟙₂` and "dualizing" isomorphisms `f^! ω₂ ≅ ω₁`. The pushforward of
`γ : 𝟙₁ ⟶ ω₁` along `f` is
`𝟙₂ ⟶ f_* f^* 𝟙₂ ⟶ f_* ω₁ ≅ f_! ω₁ ≅ f_! f^! ω₂ ⟶ ω₂`. If the composition isomorphisms of the
four functors are compatible with the units, the identifications `f_! ≅ f_*` and the
dualizing isomorphisms, then pushing forward along `f` and then `g` is pushing forward along
`F`. -/
lemma pushforward_comp_aux {fU : C₂ ⥤ C₁} {fL : C₁ ⥤ C₂} (af : fU ⊣ fL) {fS : C₁ ⥤ C₂}
    {fR : C₂ ⥤ C₁} (bf : fS ⊣ fR) (If : fS ≅ fL)
    {gU : C₃ ⥤ C₂} {gL : C₂ ⥤ C₃} (ag : gU ⊣ gL) {gS : C₂ ⥤ C₃} {gR : C₃ ⥤ C₂} (bg : gS ⊣ gR)
    (Ig : gS ≅ gL)
    {FU : C₃ ⥤ C₁} {FL : C₁ ⥤ C₃} (aF : FU ⊣ FL) {FS : C₁ ⥤ C₃} {FR : C₃ ⥤ C₁} (bF : FS ⊣ FR)
    (IF : FS ≅ FL)
    (cU : FU ≅ gU ⋙ fU) (cS : fL ⋙ gL ≅ FL)
    (hcS : cS.inv = conjugateEquiv aF (ag.comp af) cU.inv)
    (cL : FS ≅ fS ⋙ gS)
    (hI : ∀ K, cL.hom.app K ≫ Ig.hom.app (fS.obj K) ≫ gL.map (If.hom.app K) =
      IF.hom.app K ≫ cS.inv.app K)
    {e₁ : C₁} {e₂ : C₂} {e₃ : C₃} (εf : e₁ ≅ fU.obj e₂) (εg : e₂ ≅ gU.obj e₃)
    (εF : e₁ ≅ FU.obj e₃) (hε : cU.hom.app e₃ ≫ fU.map εg.inv ≫ εf.inv = εF.inv)
    {ω₁ : C₁} {ω₂ : C₂} {ω₃ : C₃} (df : fR.obj ω₂ ≅ ω₁) (dg : gR.obj ω₃ ≅ ω₂)
    (dF : FR.obj ω₃ ≅ ω₁)
    (hd : cL.hom.app ω₁ ≫ gS.map (fS.map df.inv ≫ bf.counit.app ω₂) ≫ gS.map dg.inv ≫
      bg.counit.app ω₃ = FS.map dF.inv ≫ bF.counit.app ω₃)
    (γ : e₁ ⟶ ω₁) :
    ag.unit.app e₃ ≫ gL.map (εg.inv ≫ af.unit.app e₂ ≫
        fL.map (εf.inv ≫ γ) ≫ If.inv.app ω₁ ≫ fS.map df.inv ≫ bf.counit.app ω₂) ≫
      Ig.inv.app ω₂ ≫ gS.map dg.inv ≫ bg.counit.app ω₃ =
    aF.unit.app e₃ ≫ FL.map (εF.inv ≫ γ) ≫ IF.inv.app ω₁ ≫ FS.map dF.inv ≫
      bF.counit.app ω₃ := by
  have hu := unit_conjugateEquiv aF (ag.comp af) cU.inv e₃
  rw [← hcS] at hu
  simp only [Adjunction.comp_unit_app, Functor.comp_map] at hu
  have hI' : cS.inv.app ω₁ ≫ gL.map (If.inv.app ω₁) ≫ Ig.inv.app (fS.obj ω₁) =
      IF.inv.app ω₁ ≫ cL.hom.app ω₁ := by
    rw [← cancel_epi (IF.hom.app ω₁), Iso.hom_inv_id_app_assoc, ← reassoc_of% (hI ω₁),
      ← gL.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app, Category.comp_id]
  have hε' : cU.inv.app e₃ ≫ εF.inv = fU.map εg.inv ≫ εf.inv := by
    rw [← hε, Iso.inv_hom_id_app_assoc]
  have key : εg.inv ≫ af.unit.app e₂ ≫ fL.map (εf.inv ≫ γ) =
      af.unit.app _ ≫ fL.map (cU.inv.app e₃) ≫ fL.map (εF.inv ≫ γ) := by
    have h := af.unit.naturality εg.inv
    simp only [Functor.id_map, Functor.comp_map] at h
    rw [reassoc_of% h, ← fL.map_comp, ← fL.map_comp, ← reassoc_of% hε']
  rw [← hd, ← reassoc_of% hI', cS.inv.naturality_assoc, reassoc_of% hu,
    ← Ig.inv.naturality_assoc (fS.map df.inv ≫ bf.counit.app ω₂), reassoc_of% key]
  simp only [Functor.map_comp, Functor.comp_map, Functor.id_obj, Category.assoc]

end CategoryTheory

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]

/-- **Associativity of conjugate composition isomorphisms.** Let `L_m ⊣ R_m` be a family of
adjunctions `C₁ ⥤ C₄` indexed by `m : M`, and `L_f ⊣ R_f`, `L_g ⊣ R_g`, `L_h ⊣ R_h`,
`L_{fg} ⊣ R_{fg}`, `L_{gh} ⊣ R_{gh}` adjunctions between `C₁, …, C₄`. If composition
isomorphisms `L_{m₁} ≅ L_{fg} ⋙ L_h`, `L_{fg} ≅ L_f ⋙ L_g`, `L_{m₂} ≅ L_f ⋙ L_{gh}` and
`L_{gh} ≅ L_g ⋙ L_h` of the left adjoints satisfy the associativity equation, for `m₁ = m₂`,
then so do their conjugates, the composition isomorphisms of the right adjoints. -/
lemma conjugateIsoEquiv_assoc_aux {M : Type*} (L : M → C₁ ⥤ C₄) (R : M → C₄ ⥤ C₁)
    (adj : ∀ m, L m ⊣ R m) {m₁ m₂ : M} (hm : m₁ = m₂)
    {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁} (af : Lf ⊣ Rf) {Lg : C₂ ⥤ C₃} {Rg : C₃ ⥤ C₂} (ag : Lg ⊣ Rg)
    {Lh : C₃ ⥤ C₄} {Rh : C₄ ⥤ C₃} (ah : Lh ⊣ Rh) {Lfg : C₁ ⥤ C₃} {Rfg : C₃ ⥤ C₁}
    (afg : Lfg ⊣ Rfg) {Lgh : C₂ ⥤ C₄} {Rgh : C₄ ⥤ C₂} (agh : Lgh ⊣ Rgh)
    (cfg : Lfg ≅ Lf ⋙ Lg) (cgh : Lgh ≅ Lg ⋙ Lh) (c₁ : L m₁ ≅ Lfg ⋙ Lh)
    (c₂ : L m₂ ≅ Lf ⋙ Lgh)
    (h : ∀ K, c₁.hom.app K ≫ Lh.map (cfg.hom.app K) =
      eqToHom (congrArg (fun m ↦ (L m).obj K) hm) ≫ c₂.hom.app K ≫ cgh.hom.app (Lf.obj K))
    (K' : C₄) :
    (conjugateIsoEquiv (adj m₁) (afg.comp ah) c₁.symm).hom.app K' ≫
        (conjugateIsoEquiv afg (af.comp ag) cfg.symm).hom.app (Rh.obj K') =
      eqToHom (congrArg (fun m ↦ (R m).obj K') hm) ≫
        (conjugateIsoEquiv (adj m₂) (af.comp agh) c₂.symm).hom.app K' ≫
        Rf.map ((conjugateIsoEquiv agh (ag.comp ah) cgh.symm).hom.app K') := by
  subst hm
  simp only [eqToHom_refl, Category.id_comp] at h ⊢
  have hL : Functor.whiskerRight cfg.inv Lh ≫ c₁.inv =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Lf cgh.inv ≫ c₂.inv := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Category.id_comp]
    rw [← cancel_epi (Lh.map (cfg.hom.app K)), ← cancel_epi (c₁.hom.app K),
      ← Lh.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app, reassoc_of% (h K), Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  have e := congrArg (fun τ ↦ (conjugateEquiv (adj m₁) ((af.comp ag).comp ah) τ).app K') hL
  rw [← conjugateEquiv_comp _ (afg.comp ah), ← conjugateEquiv_comp _ (af.comp (ag.comp ah)),
    ← conjugateEquiv_comp _ (af.comp agh), conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft] at e
  simpa using e

end CategoryTheory

namespace CategoryTheory

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]

/-- Let `c : F_! ≅ f_! ⋙ g_!` be a composition isomorphism of left adjoints, with conjugate
`F^! ≅ g^! ⋙ f^!`, and let `f^! ω₂ ≅ ω₁`, `g^! ω₃ ≅ ω₂`, `F^! ω₃ ≅ ω₁` be isomorphisms
compatible with the conjugate. Then the counits `F_! ω₁ ≅ F_! F^! ω₃ ⟶ ω₃` and
`g_! f_! ω₁ ≅ g_! f_! f^! ω₂ ⟶ g_! ω₂ ≅ g_! g^! ω₃ ⟶ ω₃` agree through `c`. -/
lemma lowerShriekComp_dualizingComplexComp_counit_aux {fS : C₁ ⥤ C₂} {fR : C₂ ⥤ C₁}
    (bf : fS ⊣ fR) {gS : C₂ ⥤ C₃} {gR : C₃ ⥤ C₂} (bg : gS ⊣ gR) {FS : C₁ ⥤ C₃}
    {FR : C₃ ⥤ C₁} (bF : FS ⊣ FR) (cL : FS ≅ fS ⋙ gS) {ω₁ : C₁} {ω₂ : C₂} {ω₃ : C₃}
    (df : fR.obj ω₂ ≅ ω₁) (dg : gR.obj ω₃ ≅ ω₂) (dF : FR.obj ω₃ ≅ ω₁)
    (hA : df.inv ≫ fR.map dg.inv =
      dF.inv ≫ (conjugateIsoEquiv bF (bf.comp bg) cL.symm).hom.app ω₃) :
    cL.hom.app ω₁ ≫ gS.map (fS.map df.inv ≫ bf.counit.app ω₂) ≫ gS.map dg.inv ≫
      bg.counit.app ω₃ = FS.map dF.inv ≫ bF.counit.app ω₃ := by
  have hc := conjugateEquiv_counit bF (bf.comp bg) cL.inv ω₃
  simp only [Functor.comp_map, Adjunction.comp_counit_app] at hc
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at hA
  have hn := bf.counit.naturality dg.inv
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← gS.map_comp_assoc (bf.counit.app ω₂) dg.inv, ← hn, Functor.map_comp_assoc,
    ← gS.map_comp_assoc (fS.map df.inv), ← fS.map_comp, hA, fS.map_comp, gS.map_comp_assoc, hc,
    ← Functor.comp_map fS gS dF.inv, ← cL.hom.naturality_assoc,
    Iso.hom_inv_id_app_assoc]

end CategoryTheory
