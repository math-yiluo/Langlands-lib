/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso

/-! # Compatibility of stalk comparison with a second open restriction

Source: lem-pc-finite-free-stalk-degreewise-shrink, step 3, expanding
lemma-coherent-base-change-invertible-sheaves--3's finite matrix calculation.
(blueprint: lem-pc-stalk-restriction-subopen-compatibility)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_pullback_comp {A B D : Scheme.{u}}
    (b : A ⟶ B) (c : B ⟶ D) [IsOpenImmersion b] [IsOpenImmersion c]
    (M : D.Modules) :
    (restrictFunctorIsoPullback (b ≫ c)).hom.app M ≫ (pullbackComp b c).inv.app M =
      (restrictFunctorComp b c).hom.app M ≫
        (restrictFunctor b).map ((restrictFunctorIsoPullback c).hom.app M) ≫
        (restrictFunctorIsoPullback b).hom.app ((pullback c).obj M) := by
  apply ((restrictAdjunction (b ≫ c)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  dsimp only [restrictFunctorIsoPullback]
  rw [← Category.assoc,
    (restrictAdjunction (b ≫ c)).unit_leftAdjointUniq_hom_app]
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction c).comp
    (pullbackPushforwardAdjunction b)) (pullbackPushforwardAdjunction (b ≫ c))
    (pullbackComp b c).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  rw [← h]
  rw [← (restrictAdjunction c).unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction c) M,
    ← (restrictAdjunction b).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction b) ((pullback c).obj M)]
  apply hom_ext
  intro U
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    restrictAdjunction_unit_app_app,
    restrictFunctorComp_hom_app_app]
  erw [Category.comp_id, Category.assoc]
  erw [← Category.assoc
    (Hom.app (((restrictAdjunction c).leftAdjointUniq
      (pullbackPushforwardAdjunction c)).hom.app M) (c ⁻¹ᵁ U))]
  erw [← (((restrictAdjunction c).leftAdjointUniq
    (pullbackPushforwardAdjunction c)).hom.app M).mapPresheaf.naturality
    (homOfLE (b.image_preimage_le (c ⁻¹ᵁ U))).op]
  simp only [← Category.assoc]
  change ((M.presheaf.map (homOfLE (c.image_preimage_le U)).op ≫
    M.presheaf.map (c.opensFunctor.map
      (homOfLE (b.image_preimage_le (c ⁻¹ᵁ U)))).op) ≫ _) ≫ _ = _
  simp only [← Functor.map_comp]
  congr 3

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_pullback_comp_eq {A B D : Scheme.{u}}
    (b : A ⟶ B) (c : B ⟶ D) (v : A ⟶ D)
    [IsOpenImmersion b] [IsOpenImmersion c] [IsOpenImmersion v]
    (hb : b ≫ c = v) (M : D.Modules) :
    (((restrictFunctorCongr hb).symm ≪≫ restrictFunctorComp b c).hom.app M) ≫
        (restrictFunctor b).map ((restrictFunctorIsoPullback c).hom.app M) ≫
        (restrictFunctorIsoPullback b).hom.app ((pullback c).obj M) =
      (restrictFunctorIsoPullback v).hom.app M ≫
        (pullbackComp b c ≪≫ pullbackCongr hb).inv.app M := by
  subst v
  have he : (restrictFunctorCongr (rfl : b ≫ c = b ≫ c)).inv.app M = 𝟙 _ := by
    apply hom_ext
    intro U
    simp
    rfl
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, he,
    Category.id_comp, Iso.trans_inv, pullbackCongr, eqToIso_refl, Iso.refl_inv,
    Category.id_comp] using (restrict_pullback_comp b c M).symm

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_stalk_triangle {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (v : B ⟶ D) (s : A ⟶ C) (t : A ⟶ D)
    [IsOpenImmersion b] [IsOpenImmersion c] [IsOpenImmersion v]
    (hb : b ≫ c = v) (ha : a ≫ b = s) (hs : s ≫ c = t) (hv : a ≫ v = t)
    (M : D.Modules) :
    let R := (restrictFunctorCongr hb).symm ≪≫ restrictFunctorComp b c
    let d := Functor.isoWhiskerRight (restrictFunctorIsoPullback b) (pullback a) ≪≫
      pullbackComp a b ≪≫ pullbackCongr ha
    let eU := Functor.isoWhiskerRight (restrictFunctorIsoPullback c) (pullback s) ≪≫
      pullbackComp s c ≪≫ pullbackCongr hs
    let eV := Functor.isoWhiskerRight (restrictFunctorIsoPullback v) (pullback a) ≪≫
      pullbackComp a v ≪≫ pullbackCongr hv
    (pullback a).map (R.hom.app M) ≫ d.hom.app ((restrictFunctor c).obj M) ≫
      eU.hom.app M = eV.hom.app M := by
  dsimp only
  let S := pullback a
  let T := pullback s
  let k := (restrictFunctorIsoPullback c).hom.app M
  let d := Functor.isoWhiskerRight (restrictFunctorIsoPullback b) S ≪≫
    pullbackComp a b ≪≫ pullbackCongr ha
  have hn := d.hom.naturality k
  change S.map ((restrictFunctor b).map k) ≫ d.hom.app ((pullback c).obj M) =
    d.hom.app ((restrictFunctor c).obj M) ≫ T.map k at hn
  change S.map _ ≫ d.hom.app ((restrictFunctor c).obj M) ≫
      (T.map k ≫ (pullbackComp s c ≪≫ pullbackCongr hs).hom.app M) = _
  rw [← Category.assoc (d.hom.app _), ← hn]
  dsimp only [d, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← Category.assoc (S.map _), ← S.map_comp]
  rw [← Category.assoc (S.map _), ← S.map_comp]
  have hh := restrict_pullback_comp_eq b c v hb M
  simp only [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc] at hh
  rw [hh, S.map_comp]
  have ht :
      (pullback a).map ((pullbackComp b c ≪≫ pullbackCongr hb).inv.app M) ≫
        ((pullbackComp a b ≪≫ pullbackCongr ha).hom.app ((pullback c).obj M)) ≫
        ((pullbackComp s c ≪≫ pullbackCongr hs).hom.app M) =
      ((pullbackComp a v ≪≫ pullbackCongr hv).hom.app M) := by
    subst v s t
    simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
      Category.comp_id]
    have h := congrArg (fun α ↦ α.app M) (pseudofunctor_associativity a b c)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp] at h
    apply (cancel_epi ((pullbackComp a (b ≫ c)).inv.app M)).1
    simpa using h
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc] at ht
  simp only [Category.assoc]
  rw [ht]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of the restriction of a component map is its original stalk conjugated
by the canonical comparisons. No chain equations or finiteness are required.

Source: lem-pc-finite-free-stalk-degreewise-shrink, step 3, and the comparison
calculation in lem-pc-finite-free-stalk-chain-map-lift-restrict.

Proof: Write j for V -> U and C for the comparison of restriction to V with
restriction first to U and then along j. Replace restrictions by pullbacks using
restrictFunctorIsoPullback. The equality V.fromSpecStalkOfMem >> j =
U.fromSpecStalkOfMem follows by cancelling the open inclusion U -> Y and using
fromSpecStalkOfMem_ι twice. Pullback composition gives a comparison D between
restriction along j followed by stalk pullback and stalk pullback through U.
The associativity law for pullback composition identifies the composite of the
stalk pullback of C with D with E_V followed by E_U inverse. The compatibility
of restriction-to-pullback comparisons with composition follows from their
adjunction units (equivalently uniqueness of left adjoints to the common
pushforward). Apply naturality of D to f and cancel inverse/hom pairs. Taking
the n-th component gives the displayed equation. This also covers U = V,
zero objects, and arbitrary maps between the indicated terms.
(blueprint: lem-pc-stalk-restriction-subopen-compatibility) -/
theorem stalkRestrictionComplexIso_map_subopen
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (y : Y) (U V : Y.Opens) (hyU : y ∈ U) (hyV : y ∈ V) (hVU : V ≤ U)
    (n : ℤ)
    (f : (restrictFunctor U.ι).obj (P.X n) ⟶
      (restrictFunctor U.ι).obj (Q.X n)) :
    let C := NatIso.mapHomologicalComplex
      ((restrictFunctorCongr (Y.homOfLE_ι hVU)).symm ≪≫
        restrictFunctorComp (Y.homOfLE hVU) U.ι) (ComplexShape.up ℤ)
    (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map
      (((C.app P).hom.f n) ≫ (restrictFunctor (Y.homOfLE hVU)).map f ≫
        ((C.app Q).inv.f n)) =
      ((stalkRestrictionComplexIso V y hyV).app P).hom.f n ≫
        ((stalkRestrictionComplexIso U y hyU).app P).inv.f n ≫
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map f ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).hom.f n ≫
        ((stalkRestrictionComplexIso V y hyV).app Q).inv.f n := by
  dsimp only [stalkRestrictionComplexIso, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]
  have ha : V.fromSpecStalkOfMem y hyV ≫ Y.homOfLE hVU =
      U.fromSpecStalkOfMem y hyU := by
    apply (cancel_mono U.ι).1
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  let S := pullback (V.fromSpecStalkOfMem y hyV)
  let T := pullback (U.fromSpecStalkOfMem y hyU)
  let R := restrictFunctor (Y.homOfLE hVU)
  let C := (restrictFunctorCongr (Y.homOfLE_ι hVU)).symm ≪≫
    restrictFunctorComp (Y.homOfLE hVU) U.ι
  let d := Functor.isoWhiskerRight (restrictFunctorIsoPullback (Y.homOfLE hVU)) S ≪≫
    pullbackComp (V.fromSpecStalkOfMem y hyV) (Y.homOfLE hVU) ≪≫ pullbackCongr ha
  let eU := Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) T ≪≫
    pullbackComp (U.fromSpecStalkOfMem y hyU) U.ι ≪≫
      pullbackCongr (U.fromSpecStalkOfMem_ι y hyU)
  let eV := Functor.isoWhiskerRight (restrictFunctorIsoPullback V.ι) S ≪≫
    pullbackComp (V.fromSpecStalkOfMem y hyV) V.ι ≪≫
      pullbackCongr (V.fromSpecStalkOfMem_ι y hyV)
  have hc (M : Y.Modules) :
      S.map (C.hom.app M) ≫ d.hom.app ((restrictFunctor U.ι).obj M) ≫
        eU.hom.app M = eV.hom.app M :=
    restrict_stalk_triangle (V.fromSpecStalkOfMem y hyV) (Y.homOfLE hVU) U.ι V.ι
      (U.fromSpecStalkOfMem y hyU) (Y.fromSpecStalk y) (Y.homOfLE_ι hVU) ha
      (U.fromSpecStalkOfMem_ι y hyU) (V.fromSpecStalkOfMem_ι y hyV) M
  have hi (M : Y.Modules) : S.map (C.inv.app M) =
      d.hom.app ((restrictFunctor U.ι).obj M) ≫ eU.hom.app M ≫ eV.inv.app M := by
    apply (cancel_epi (S.map (C.hom.app M))).1
    rw [← Functor.map_comp, C.hom_inv_id_app, S.map_id]
    calc
      _ = eV.hom.app M ≫ eV.inv.app M := (eV.hom_inv_id_app M).symm
      _ = _ := by rw [← hc M]; simp only [Category.assoc]
  have hp (M : Y.Modules) : S.map (C.hom.app M) ≫ d.hom.app ((restrictFunctor U.ι).obj M) =
      eV.hom.app M ≫ eU.inv.app M := by
    apply (cancel_mono (eU.hom.app M)).1
    simpa only [Category.assoc, eU.inv_hom_id_app, Category.comp_id] using hc M
  have hd := d.hom.naturality f
  change S.map (R.map f) ≫ d.hom.app ((restrictFunctor U.ι).obj (Q.X n)) =
    d.hom.app ((restrictFunctor U.ι).obj (P.X n)) ≫ T.map f at hd
  change S.map (C.hom.app (P.X n) ≫ R.map f ≫ C.inv.app (Q.X n)) =
    eV.hom.app (P.X n) ≫ eU.inv.app (P.X n) ≫ T.map f ≫
      eU.hom.app (Q.X n) ≫ eV.inv.app (Q.X n)
  simp only [Functor.map_comp]
  rw [hi]
  rw [← Category.assoc _ _ (eU.hom.app (Q.X n) ≫ eV.inv.app (Q.X n)), hd]
  calc
    _ = (S.map (C.hom.app (P.X n)) ≫ d.hom.app ((restrictFunctor U.ι).obj (P.X n))) ≫ T.map f ≫
        eU.hom.app (Q.X n) ≫ eV.inv.app (Q.X n) := by simp only [Category.assoc]
    _ = _ := by rw [hp]; simp only [Category.assoc]


end AlgebraicGeometry.Scheme.Modules
