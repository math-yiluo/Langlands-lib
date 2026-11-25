/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Conjugates of composition isomorphisms

Two formal facts about conjugate natural transformations of composite adjunctions:

* `CategoryTheory.conjugateIsoEquiv_comp_left_hom_app`: if `c : L_F ≅ G ⋙ L_h` and `ι : G ≅ 𝟭`
  compose to `e : L_F ≅ L_h`, then the conjugates compose to the conjugate of `e` (the left unit
  law of conjugate composition isomorphisms);
* `CategoryTheory.Adjunction.ofNatIsoRight_comp_unit_app`: for adjunctions `L ⊣ S` obtained from
  adjunctions `L ⊣ R` through isomorphisms `S ≅ R`, a composition isomorphism `c_S` of the `S`
  which corresponds to the conjugate of a composition isomorphism `c_L` of the `L` is compatible
  with the units.
-/

@[expose] public section

namespace CategoryTheory

section Left

variable {C D : Type*} [Category C] [Category D]

/-- Let `c : L_F ≅ G ⋙ L_h` and `ι : G ≅ 𝟭` be isomorphisms of left adjoints whose composite is
`e : L_F ≅ L_h`. Then the conjugates `R_F ≅ R_h ⋙ R_G` of `c` and `R_G ≅ 𝟭` of `ι` compose to
the conjugate `R_F ≅ R_h` of `e`:
```
R_F ──conj(c)──▶ R_G R_h ──conj(ι)──▶ R_h
  ╲                                    ╱
   ╰──────────── conj(e) ────────────╯
```
-/
lemma conjugateIsoEquiv_comp_left_hom_app {LF Lh : C ⥤ D} {RF Rh : D ⥤ C} {G RG : C ⥤ C}
    (adjF : LF ⊣ RF) (adjh : Lh ⊣ Rh) (adjG : G ⊣ RG) (c : LF ≅ G ⋙ Lh) (ι : G ≅ 𝟭 C)
    (e : LF ≅ Lh) (hc : ∀ K, c.hom.app K ≫ Lh.map (ι.hom.app K) = e.hom.app K) (K' : D) :
    (conjugateIsoEquiv adjF (adjG.comp adjh) c.symm).hom.app K' ≫
        (conjugateIsoEquiv adjG Adjunction.id ι.symm).hom.app (Rh.obj K') =
      (conjugateIsoEquiv adjF adjh e.symm).hom.app K' := by
  apply (adjh.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  have hι := conjugateEquiv_counit adjG Adjunction.id ι.inv (Rh.obj K')
  have hC := conjugateEquiv_counit adjF (adjG.comp adjh) c.inv K'
  have hE := conjugateEquiv_counit adjF adjh e.inv K'
  simp only [Functor.id_obj, Functor.id_map, Adjunction.id_counit, NatTrans.id_app] at hι
  erw [Category.comp_id] at hι
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at hC
  have he : Lh.map (ι.inv.app (RF.obj K')) ≫ c.inv.app (RF.obj K') = e.inv.app (RF.obj K') := by
    rw [← cancel_mono (e.hom.app _), Category.assoc, Iso.inv_hom_id_app, ← hc,
      Iso.inv_hom_id_app_assoc, ← Lh.map_comp, Iso.inv_hom_id_app]
    simp
  have hn := ι.inv.naturality ((conjugateEquiv adjF (adjG.comp adjh) c.inv).app K')
  simp only [Functor.id_obj, Functor.id_map] at hn
  rw [hE, hι, ← he, Category.assoc, ← hC]
  simp only [← Functor.map_comp_assoc]
  erw [reassoc_of% hn]

end Left

section Units

variable {CX CY CZ : Type*} [Category CX] [Category CY] [Category CZ]
  {Lf : CY ⥤ CX} {Rf Sf : CX ⥤ CY} {Lg : CZ ⥤ CY} {Rg Sg : CY ⥤ CZ}
  {Lfg : CZ ⥤ CX} {Rfg Sfg : CX ⥤ CZ}

/-- Let `L_f ⊣ R_f`, `L_g ⊣ R_g`, `L_{fg} ⊣ R_{fg}` be adjunctions with isomorphisms
`S_f ≅ R_f`, `S_g ≅ R_g`, `S_{fg} ≅ R_{fg}`, and let `c_L : L_{fg} ≅ L_g ⋙ L_f` and
`c_S : S_{fg} ≅ S_f ⋙ S_g` be composition isomorphisms such that `c_S` corresponds to the
conjugate `R_{fg} ⟶ R_f ⋙ R_g` of `c_L⁻¹` (`hI`). Then the units of the adjunctions
`L ⊣ S` are compatible with `c_L` and `c_S`. -/
lemma Adjunction.ofNatIsoRight_comp_unit_app (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (afg : Lfg ⊣ Rfg)
    (iF : Sf ≅ Rf) (iG : Sg ≅ Rg) (iFG : Sfg ≅ Rfg) (cL : Lfg ≅ Lg ⋙ Lf)
    (cS : Sfg ≅ Sf ⋙ Sg)
    (hI : ∀ K, cS.hom.app K ≫ iG.hom.app (Sf.obj K) ≫ Rg.map (iF.hom.app K) =
      iFG.hom.app K ≫ (conjugateEquiv afg (ag.comp af) cL.inv).app K) (c : CZ) :
    (afg.ofNatIsoRight iFG.symm).unit.app c ≫ cS.hom.app (Lfg.obj c) ≫
        Sg.map (Sf.map (cL.hom.app c)) =
      (ag.ofNatIsoRight iG.symm).unit.app c ≫
        Sg.map ((af.ofNatIsoRight iF.symm).unit.app (Lg.obj c)) := by
  have hI' : iFG.inv.app (Lfg.obj c) ≫ cS.hom.app (Lfg.obj c) =
      (conjugateEquiv afg (ag.comp af) cL.inv).app (Lfg.obj c) ≫
        Rg.map (iF.inv.app (Lfg.obj c)) ≫ iG.inv.app (Sf.obj (Lfg.obj c)) := by
    rw [← cancel_epi (iFG.hom.app _), Iso.hom_inv_id_app_assoc, ← reassoc_of% (hI _),
      ← Rg.map_comp_assoc, Iso.hom_inv_id_app]
    simp
  have hU := unit_conjugateEquiv afg (ag.comp af) cL.inv c
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_unit_app] at hU
  have hn₁ := iG.inv.naturality (af.unit.app (Lg.obj c) ≫ Rf.map (cL.inv.app c) ≫
    iF.inv.app (Lfg.obj c))
  have hn₂ := iF.inv.naturality (cL.inv.app c)
  simp only [Functor.id_obj, Functor.comp_obj] at hn₁ hn₂
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hI', reassoc_of% hU]
  simp only [← Rg.map_comp_assoc]
  erw [reassoc_of% hn₁]
  rw [← Sg.map_comp]
  congr 3
  simp only [Category.assoc]
  rw [reassoc_of% hn₂, ← Sf.map_comp, Iso.inv_hom_id_app]
  simp

end Units

section BaseChange

variable {CC CF CX CP : Type*} [Category CC] [Category CF] [Category CX] [Category CP]
  {ιs : CC ⥤ CF} {Lι Sι : CF ⥤ CC} (Bι : ιs ⊣ Sι) (σι : Lι ≅ Sι)
  {Δs : CP ⥤ CX} {LΔ SΔ : CX ⥤ CP} (BΔ : Δs ⊣ SΔ) (σΔ : LΔ ≅ SΔ)
  {Lc : CC ⥤ CP} {Rc : CP ⥤ CC} (Ac : Lc ⊣ Rc) {Ld : CF ⥤ CX} {Rd : CX ⥤ CF} (Ad : Ld ⊣ Rd)
  (Sq : Lι ⋙ Lc ≅ Ld ⋙ LΔ)

/-- The exceptional adjoint of the right-adjoint form of a base change isomorphism which is the
mate of a square isomorphism. For a square isomorphism `Sq : Lι ⋙ Lc ≅ Ld ⋙ LΔ`, its mate
`Ex : Lc ⋙ Δ^* ⟶ ι^* ⋙ Ld` for `ι^* ⊣ Lι`, `Δ^* ⊣ LΔ` (with `Lι ≅ Sι`, `LΔ ≅ SΔ`), and the
conjugate `U : SΔ ⋙ Rc ≅ Rd ⋙ Sι` of `Ex⁻¹`, the `Lc ⊣ Rc`-adjoint of `U⁻¹` is
```
Lc Sι Rd N ──Lc σι⁻¹──▶ Lc Lι Rd N ──Sq──▶ LΔ Ld Rd N ──LΔ ε──▶ LΔ N ──σΔ──▶ SΔ N.
```
-/
lemma Adjunction.homEquiv_symm_conjugateIsoEquiv_inv_app (Ex : Lc ⋙ Δs ⟶ ιs ⋙ Ld) [IsIso Ex]
    (hEx : Ex = (mateEquiv (Bι.ofNatIsoRight σι.symm) (BΔ.ofNatIsoRight σΔ.symm)).symm Sq.hom)
    (N : CX) :
    (Ac.homEquiv _ _).symm ((conjugateIsoEquiv (Ac.comp BΔ) (Bι.comp Ad)
      (asIso Ex).symm).inv.app N) =
      Lc.map (σι.inv.app (Rd.obj N)) ≫ Sq.hom.app (Rd.obj N) ≫ LΔ.map (Ad.counit.app N) ≫
        σΔ.hom.app N := by
  subst hEx
  rw [Equiv.symm_apply_eq]
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj, mateEquiv_symm_apply, ofNatIsoRight_unit,
    Iso.symm_hom, Functor.whiskerRight_comp, ofNatIsoRight_counit, Iso.symm_inv,
    Functor.whiskerLeft_comp, Category.assoc, conjugateIsoEquiv_apply_inv, asIso_hom,
    conjugateEquiv_apply_app, comp_unit_app, NatTrans.comp_app, Functor.id_obj,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.map_id, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
    Functor.map_comp, comp_counit_app, NatTrans.naturality]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp]
  have h1 := BΔ.unit.naturality_assoc (Lc.map (Bι.unit.app (Sι.obj (Rd.obj N))) ≫
    Lc.map (σι.inv.app (ιs.obj (Sι.obj (Rd.obj N)))) ≫
    Sq.hom.app (ιs.obj (Sι.obj (Rd.obj N))) ≫
    σΔ.hom.app (Ld.obj (ιs.obj (Sι.obj (Rd.obj N)))))
    (SΔ.map (BΔ.counit.app (Ld.obj (ιs.obj (Sι.obj (Rd.obj N))))) ≫
      SΔ.map (Ld.map (Bι.counit.app (Rd.obj N))) ≫ SΔ.map (Ad.counit.app N))
  simp only [Functor.id_map, Functor.comp_map, Functor.map_comp, Category.assoc] at h1
  dsimp only [Functor.id_obj] at h1
  rw [← h1]
  rw [BΔ.right_triangle_components_assoc]
  have h2 := σΔ.hom.naturality (Ld.map (Bι.counit.app (Rd.obj N)))
  have h3 := Sq.hom.naturality (Bι.counit.app (Rd.obj N))
  have h4 := σι.inv.naturality (Bι.counit.app (Rd.obj N))
  simp only [Functor.comp_map] at h2 h3 h4
  have key : Bι.unit.app (Sι.obj (Rd.obj N)) ≫ σι.inv.app (ιs.obj (Sι.obj (Rd.obj N))) ≫
      Lι.map (Bι.counit.app (Rd.obj N)) = σι.inv.app (Rd.obj N) := by
    dsimp only [Functor.comp_obj] at h4
    rw [← h4, ← Category.assoc, Bι.right_triangle_components]
    simp
  rw [← reassoc_of% h2, ← reassoc_of% h3, ← Lc.map_comp_assoc, ← Lc.map_comp_assoc]
  simp only [Category.assoc]
  rw [key]

end BaseChange

end CategoryTheory
