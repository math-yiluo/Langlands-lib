/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso

/-! # Restriction stability of a local chain map

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix extension argument, expanded
in lem-pc-finite-free-stalk-chain-map-lift.
(blueprint: lem-pc-finite-free-stalk-chain-map-lift-restrict)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
private theorem pullback_triangle {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (v : B ⟶ D) (s : A ⟶ C) (t : A ⟶ D)
    (hb : b ≫ c = v) (ha : a ≫ b = s) (hs : s ≫ c = t) (hv : a ≫ v = t)
    (M : D.Modules) :
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

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_triangle {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (v : B ⟶ D) (s : A ⟶ C) (t : A ⟶ D)
    [IsOpenImmersion c] [IsOpenImmersion v]
    (hb : b ≫ c = v) (ha : a ≫ b = s) (hs : s ≫ c = t) (hv : a ≫ v = t)
    (P Q : CochainComplex D.Modules ℤ)
    (f : ((pullback t).mapHomologicalComplex _).obj P ⟶
      ((pullback t).mapHomologicalComplex _).obj Q)
    (fU : ((restrictFunctor c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((restrictFunctor c).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (h : ((pullback s).mapHomologicalComplex (ComplexShape.up ℤ)).map fU =
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerRight (restrictFunctorIsoPullback c) (pullback s) ≪≫
          pullbackComp s c ≪≫ pullbackCongr hs) (ComplexShape.up ℤ)).app P).hom ≫ f ≫
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerRight (restrictFunctorIsoPullback c) (pullback s) ≪≫
          pullbackComp s c ≪≫ pullbackCongr hs) (ComplexShape.up ℤ)).app Q).inv) :
    ∃ (fV : ((restrictFunctor v).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
        ((restrictFunctor v).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q),
      ((pullback a).mapHomologicalComplex (ComplexShape.up ℤ)).map fV =
        ((Functor.mapHomologicalComplexCompIso
          (Functor.isoWhiskerRight (restrictFunctorIsoPullback v) (pullback a) ≪≫
            pullbackComp a v ≪≫ pullbackCongr hv) (ComplexShape.up ℤ)).app P).hom ≫ f ≫
        ((Functor.mapHomologicalComplexCompIso
          (Functor.isoWhiskerRight (restrictFunctorIsoPullback v) (pullback a) ≪≫
            pullbackComp a v ≪≫ pullbackCongr hv) (ComplexShape.up ℤ)).app Q).inv := by
  let I := ComplexShape.up ℤ
  let R := (pullback b).mapHomologicalComplex I
  let S := (pullback a).mapHomologicalComplex I
  let T := (pullback s).mapHomologicalComplex I
  let kU := NatIso.mapHomologicalComplex (restrictFunctorIsoPullback c) I
  let kV := NatIso.mapHomologicalComplex (restrictFunctorIsoPullback v) I
  let C := (Functor.mapHomologicalComplexCompIso
    (pullbackComp b c ≪≫ pullbackCongr hb) I).symm
  let d := Functor.mapHomologicalComplexCompIso
    (pullbackComp a b ≪≫ pullbackCongr ha) I
  let eU := Functor.mapHomologicalComplexCompIso (pullbackComp s c ≪≫ pullbackCongr hs) I
  let eV := Functor.mapHomologicalComplexCompIso (pullbackComp a v ≪≫ pullbackCongr hv) I
  let gU := (kU.app P).inv ≫ fU ≫ (kU.app Q).hom
  let gV := (C.app P).hom ≫ R.map gU ≫ (C.app Q).inv
  refine ⟨(kV.app P).hom ≫ gV ≫ (kV.app Q).inv, ?_⟩
  have hc (M : CochainComplex D.Modules ℤ) :
      S.map (C.app M).hom ≫ (d.app (((pullback c).mapHomologicalComplex I).obj M)).hom ≫
        (eU.app M).hom = (eV.app M).hom := by
    ext n : 1
    exact pullback_triangle a b c v s t hb ha hs hv (M.X n)
  change T.map fU = (T.map (kU.app P).hom ≫ (eU.app P).hom) ≫ f ≫
    ((eU.app Q).inv ≫ T.map (kU.app Q).inv) at h
  have hu : T.map gU = (eU.app P).hom ≫ f ≫ (eU.app Q).inv := by
    simp only [gU, Functor.map_comp]
    rw [h]
    have hp : T.map (kU.app P).inv ≫ T.map (kU.app P).hom = 𝟙 _ := by
      rw [← T.map_comp, Iso.inv_hom_id, T.map_id]
    have hq : T.map (kU.app Q).inv ≫ T.map (kU.app Q).hom = 𝟙 _ := by
      rw [← T.map_comp, Iso.inv_hom_id, T.map_id]
    calc
      _ = (T.map (kU.app P).inv ≫ T.map (kU.app P).hom) ≫ (eU.app P).hom ≫ f ≫
          (eU.app Q).inv ≫ (T.map (kU.app Q).inv ≫ T.map (kU.app Q).hom) := by
        simp only [Category.assoc]
      _ = _ := by
        rw [hp, hq, Category.id_comp]
        change (eU.app P).hom ≫ f ≫ ((eU.app Q).inv ≫ 𝟙 _) = _
        rw [Category.comp_id]
  have hd := d.hom.naturality gU
  change S.map (R.map gU) ≫ (d.app _).hom = (d.app _).hom ≫ T.map gU at hd
  have hi (M : CochainComplex D.Modules ℤ) :
      S.map (C.app M).inv = (d.app (((pullback c).mapHomologicalComplex I).obj M)).hom ≫
        (eU.app M).hom ≫ (eV.app M).inv := by
    apply (cancel_epi (S.map (C.app M).hom)).1
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    calc
      _ = (eV.app M).hom ≫ (eV.app M).inv := (Iso.hom_inv_id _).symm
      _ = (S.map (C.app M).hom ≫ (d.app _).hom ≫ (eU.app M).hom) ≫
          (eV.app M).inv := by rw [hc]
      _ = _ := by simp only [Category.assoc]
  rw [Functor.map_comp, Functor.map_comp]
  change S.map (kV.app P).hom ≫ S.map gV ≫ S.map (kV.app Q).inv = _
  have hg : S.map gV = (eV.app P).hom ≫ f ≫ (eV.app Q).inv := by
    dsimp only [gV]
    rw [Functor.map_comp, Functor.map_comp, hi]
    rw [← Category.assoc _ _ ((eU.app Q).hom ≫ (eV.app Q).inv)]
    rw [hd]
    rw [hu]
    calc
      _ = (S.map (C.app P).hom ≫ (d.app _).hom ≫ (eU.app P).hom) ≫ f ≫
          (eV.app Q).inv := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := by rw [hc]
  rw [hg]
  change S.map (kV.app P).hom ≫ ((eV.app P).hom ≫ f ≫ (eV.app Q).inv) ≫
      S.map (kV.app Q).inv =
    (S.map (kV.app P).hom ≫ (eV.app P).hom) ≫ f ≫
      ((eV.app Q).inv ≫ S.map (kV.app Q).inv)
  simp only [Category.assoc]

/-- Restriction stability of a local chain map.

Source: lem-pc-finite-free-stalk-chain-map-lift, proof step 4, expanding
lemma-coherent-base-change-invertible-sheaves--3's extension of the finite calculation. The
comparison uses Mathlib's restrictFunctorComp, restrictFunctorIsoPullback, pullbackComp, and
pseudofunctor_associativity.

Proof: Fix V <= U containing y and let j : V.toScheme -> U.toScheme be the open
inclusion. Let R_U, R_V and R_j denote termwise restriction. The identity
j >> U.ι = V.ι and restrictFunctorComp give a natural isomorphism
C : R_V ~= R_U >> R_j. Define
fV = C(P).hom >> R_j.map fU >> C(Q).inv.
Write S_U and S_V for the corresponding termwise stalk pullbacks. Since the
map Spec O_{Y,y} -> U factors through V, restriction followed by stalk pullback
gives a natural isomorphism D : R_j >> S_V ~= S_U (with the same source Spec).
The composite S_V.mapIso C(M) followed by D(R_U M) equals E_V(M) followed by
E_U(M).symm. Indeed replace each restriction by pullback using
restrictFunctorIsoPullback, use pullback composition, and apply
pseudofunctor_associativity to the three scheme maps from the stalk through V
and U to Y. The equality of their composites is fromSpecStalkOfMem_ι;
compatibility of restrictFunctorIsoPullback with composition follows from the
uniqueness of left adjoints to the composite pushforward, or its adjunction units.
Naturality of D gives
S_V.map fV = E_V(P).hom >> E_U(P).inv >> S_U.map fU >>
  E_U(Q).hom >> E_V(Q).inv.
Substitute the hypothesis h and cancel the E_U inverse/hom pairs to obtain the
required equation. For V = U this is the same cancellation; zero complexes need
no additional hypotheses. No boundedness or finite freeness is used.
(blueprint: lem-pc-finite-free-stalk-chain-map-lift-restrict) -/
theorem restrict_chainMap_of_stalk_local
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ) (y : Y) (U : Y.Opens)
    (hyU : y ∈ U)
    (f : ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P ⟶
      ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q)
    (fU : ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (h : ((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map fU =
      ((stalkRestrictionComplexIso U y hyU).app P).hom ≫ f ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).inv) :
    ∀ (V : Y.Opens) (hyV : y ∈ V), V ≤ U →
      let R := (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)
      let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let eP := (stalkRestrictionComplexIso V y hyV).app P
      let eQ := (stalkRestrictionComplexIso V y hyV).app Q
      ∃ (fV : R.obj P ⟶ R.obj Q), S.map fV = eP.hom ≫ f ≫ eQ.inv := by
  intro V hyV hVU
  have ha : V.fromSpecStalkOfMem y hyV ≫ Y.homOfLE hVU =
      U.fromSpecStalkOfMem y hyU := by
    apply (cancel_mono U.ι).1
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact restrict_triangle (V.fromSpecStalkOfMem y hyV) (Y.homOfLE hVU) U.ι V.ι
    (U.fromSpecStalkOfMem y hyU) (Y.fromSpecStalk y) (Scheme.homOfLE_ι Y hVU) ha
    (U.fromSpecStalkOfMem_ι y hyU) (V.fromSpecStalkOfMem_ι y hyV) P Q f fU h
end AlgebraicGeometry.Scheme.Modules
