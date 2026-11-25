/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # The ordinary inverse square under source-isomorphism transport

Source: Stacks Project, Tags 0ATR and 0D5S.
-/

@[expose] public section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem source_transport_counit
    {C D T : Type*} [Category C] [Category D] [Category T]
    {L : C ⥤ D} {R : D ⥤ C} {V : D ⥤ T} {W : T ⥤ D}
    {L₀ : C ⥤ T} {R₀ : T ⥤ C}
    (a : L ⊣ R) (v : V ⊣ W) (a₀ : L₀ ⊣ R₀)
    (c : L ⋙ V ≅ L₀) (E : D) :
    let k := conjugateIsoEquiv a₀ (a.comp v) c
    let d := R.map (v.unit.app E) ≫ k.inv.app (V.obj E)
    L₀.map d ≫ a₀.counit.app (V.obj E) =
      c.inv.app (R.obj E) ≫ V.map (a.counit.app E) := by
  intro k d
  have hk : L₀.map (k.inv.app (V.obj E)) ≫ a₀.counit.app (V.obj E) =
      c.inv.app (W.obj (V.obj E) |> R.obj) ≫
        (V.map (a.counit.app (W.obj (V.obj E))) ≫ v.counit.app (V.obj E)) := by
    simpa only [k, conjugateIsoEquiv_apply_inv, Adjunction.comp_counit_app,
      Functor.comp_obj] using
      conjugateEquiv_counit (a.comp v) a₀ c.inv (V.obj E)
  dsimp only [d]
  rw [L₀.map_comp, Category.assoc, hk]
  rw [reassoc_of% c.inv.naturality (R.map (v.unit.app E))]
  change _ ≫ V.map (L.map (R.map (v.unit.app E))) ≫
    V.map (a.counit.app (W.obj (V.obj E))) ≫ _ = _
  rw [← V.map_comp_assoc]
  erw [a.counit.naturality (v.unit.app E)]
  simp only [V.map_comp, Functor.id_obj, Functor.id_map, Category.assoc]
  rw [v.left_triangle_components, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem source_mate_transport
    {C B D F T U : Type*}
    [Category C] [Category B] [Category D] [Category F] [Category T] [Category U]
    {L : C ⥤ D} {R : D ⥤ C} {M : B ⥤ F} {Q : F ⥤ B}
    {L₀ : C ⥤ T} {R₀ : T ⥤ C} {M₀ : B ⥤ U} {Q₀ : U ⥤ B}
    {K : C ⥤ B} {H : D ⥤ F} {H₀ : T ⥤ U} {V : D ⥤ T} {V' : F ⥤ U}
    (a : L ⊣ R) (b : M ⊣ Q) (a₀ : L₀ ⊣ R₀) (b₀ : M₀ ⊣ Q₀)
    (cf : L ⋙ V ≅ L₀) (cf' : M ⋙ V' ≅ M₀) (ch : H ⋙ V' ≅ V ⋙ H₀)
    (q : K ⋙ M ≅ L ⋙ H) (q₀ : K ⋙ M₀ ≅ L₀ ⋙ H₀)
    (hq : ∀ Z : C,
      V'.map (q.hom.app Z) ≫ ch.hom.app (L.obj Z) ≫ H₀.map (cf.hom.app Z) =
        cf'.hom.app (K.obj Z) ≫ q₀.hom.app Z)
    (E : D) (E' : F) (φ : H.obj E ⟶ E')
    (d : R.obj E ⟶ R₀.obj (V.obj E)) (d' : Q.obj E' ⟶ Q₀.obj (V'.obj E'))
    (hd : L₀.map d ≫ a₀.counit.app (V.obj E) =
      cf.inv.app (R.obj E) ≫ V.map (a.counit.app E))
    (hd' : M₀.map d' ≫ b₀.counit.app (V'.obj E') =
      cf'.inv.app (Q.obj E') ≫ V'.map (b.counit.app E')) :
    (b.homEquiv _ _ (q.hom.app (R.obj E) ≫ H.map (a.counit.app E)) ≫ Q.map φ) ≫ d' =
      K.map d ≫
        (b₀.homEquiv _ _ (q₀.hom.app (R₀.obj (V.obj E)) ≫
          H₀.map (a₀.counit.app (V.obj E))) ≫
          Q₀.map (ch.inv.app E ≫ V'.map φ)) := by
  let z := q.hom.app (R.obj E) ≫ H.map (a.counit.app E)
  let z₀ := q₀.hom.app (R₀.obj (V.obj E)) ≫ H₀.map (a₀.counit.app (V.obj E))
  have hb : M.map (b.homEquiv _ _ z ≫ Q.map φ) ≫ b.counit.app E' = z ≫ φ := by
    rw [M.map_comp, Category.assoc]
    erw [b.counit.naturality φ]
    rw [← Category.assoc]
    exact congrArg (fun x ↦ x ≫ φ)
      ((b.homEquiv _ _).symm_apply_apply z)
  have hb₀ : M₀.map (b₀.homEquiv _ _ z₀ ≫
      Q₀.map (ch.inv.app E ≫ V'.map φ)) ≫ b₀.counit.app (V'.obj E') =
        z₀ ≫ ch.inv.app E ≫ V'.map φ := by
    rw [M₀.map_comp, Category.assoc]
    erw [b₀.counit.naturality (ch.inv.app E ≫ V'.map φ)]
    rw [← Category.assoc]
    exact congrArg (fun x ↦ x ≫ (ch.inv.app E ≫ V'.map φ))
      ((b₀.homEquiv _ _).symm_apply_apply z₀)
  apply (b₀.homEquiv _ _).symm.injective
  change M₀.map ((b.homEquiv _ _ z ≫ Q.map φ) ≫ d') ≫
      b₀.counit.app (V'.obj E') =
    M₀.map (K.map d ≫ (b₀.homEquiv _ _ z₀ ≫
      Q₀.map (ch.inv.app E ≫ V'.map φ))) ≫ b₀.counit.app (V'.obj E')
  rw [M₀.map_comp, Category.assoc, hd']
  erw [reassoc_of% cf'.inv.naturality (b.homEquiv _ _ z ≫ Q.map φ)]
  change cf'.inv.app (K.obj (R.obj E)) ≫
      V'.map (M.map (b.homEquiv _ _ z ≫ Q.map φ)) ≫ V'.map (b.counit.app E') = _
  rw [← V'.map_comp, hb]
  rw [M₀.map_comp]
  simp only [Category.assoc]
  rw [hb₀]
  dsimp only [z₀]
  simp only [Category.assoc]
  erw [reassoc_of% q₀.hom.naturality d]
  change _ = q₀.hom.app (R.obj E) ≫ H₀.map (L₀.map d) ≫
    H₀.map (a₀.counit.app (V.obj E)) ≫ ch.inv.app E ≫ V'.map φ
  rw [← H₀.map_comp_assoc, hd, H₀.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% ch.inv.naturality (a.counit.app E)]
  change _ = q₀.hom.app (R.obj E) ≫ H₀.map (cf.inv.app (R.obj E)) ≫
    ch.inv.app (L.obj (R.obj E)) ≫ V'.map (H.map (a.counit.app E)) ≫ V'.map φ
  have hs : q₀.hom.app (R.obj E) ≫ H₀.map (cf.inv.app (R.obj E)) ≫
      ch.inv.app (L.obj (R.obj E)) =
        cf'.inv.app (K.obj (R.obj E)) ≫ V'.map (q.hom.app (R.obj E)) := by
    have hh := congrArg (fun z ↦ cf'.inv.app (K.obj (R.obj E)) ≫ z ≫
      H₀.map (cf.inv.app (R.obj E)) ≫ ch.inv.app (L.obj (R.obj E))) (hq (R.obj E))
    simp only [Category.assoc, ← H₀.map_comp_assoc, Iso.hom_inv_id_app,
      Iso.inv_hom_id_app_assoc] at hh
    erw [H₀.map_id] at hh
    simp only [Category.id_comp, Iso.hom_inv_id_app] at hh
    dsimp only [Functor.comp_obj] at hh ⊢
    simpa only [Category.comp_id] using hh.symm
  rw [reassoc_of% hs]
  simp only [z, V'.map_comp, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_source_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l))
    (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
        Functor.associator (derivedPullback g) (derivedPullback f)
            (derivedPullback h) ≪≫
          Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
              (Category.assoc h f g)))
    {X X' S S' T T' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (v : T ⟶ X) (v' : T' ⟶ X') (t : T' ⟶ T)
    (ht : t ≫ v = v' ≫ g') (h₀ : t ≫ (v ≫ f) = (v' ≫ f') ≫ g)
    (Z : schemeDerivedCategory S) :
    (derivedPullback v').map
        ((c f' g).hom.app Z ≫
          eqToHom (congrArg (fun k ↦ (derivedPullback k).obj Z) h.symm) ≫
          (c g' f).inv.app Z) ≫
      ((c v' g').hom.app ((derivedPullback f).obj Z) ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj
          ((derivedPullback f).obj Z)) ht.symm) ≫
        (c t v).inv.app ((derivedPullback f).obj Z)) ≫
      (derivedPullback t).map ((c v f).hom.app Z) =
    (c v' f').hom.app ((derivedPullback g).obj Z) ≫
      ((c (v' ≫ f') g).hom.app Z ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj Z) h₀.symm) ≫
        (c t (v ≫ f)).inv.app Z) := by
  have hf := congrArg (fun z ↦ z.hom.app Z) (hc t v f)
  have hl := congrArg (fun z ↦ z.hom.app Z) (hc v' g' f)
  have hr := congrArg (fun z ↦ z.hom.app Z) (hc v' f' g)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app, Category.id_comp] at hf hl hr
  apply (cancel_mono ((c t (v ≫ f)).hom.app Z)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hf, Iso.inv_hom_id_app_assoc]
  have hn := eqToHom_naturality (fun k : T' ⟶ X ↦ (c k f).hom.app Z) ht.symm
  rw [← reassoc_of% hn]
  have ha : (c v' g').hom.app ((derivedPullback f).obj Z) ≫
      (c (v' ≫ g') f).hom.app Z =
    (derivedPullback v').map ((c g' f).hom.app Z) ≫
      (c v' (g' ≫ f)).hom.app Z ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj Z)
        (Category.assoc v' g' f).symm) := by
    apply (cancel_mono (eqToHom (congrArg
      (fun k ↦ (derivedPullback k).obj Z) (Category.assoc v' g' f)))).mp
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hl.symm
  rw [reassoc_of% ha]
  rw [← Functor.map_comp_assoc (derivedPullback v')
    ((c g' f).inv.app Z) ((c g' f).hom.app Z), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  have hm : (derivedPullback v').map
      (eqToHom (congrArg (fun k ↦ (derivedPullback k).obj Z) h.symm)) ≫
      (c v' (g' ≫ f)).hom.app Z =
    (c v' (f' ≫ g)).hom.app Z ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback (v' ≫ k)).obj Z) h.symm) := by
    simpa only [Iso.app_hom, eqToHom_map] using
      (eqToHom_iso_hom_naturality (fun k : X' ⟶ S ↦ (c v' k).app Z) h.symm).symm
  rw [reassoc_of% hm, reassoc_of% hr]
  simp only [eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_source_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X U V V' S T : Scheme.{u}}
    (f : X ⟶ S) (f₀ : U ⟶ S) (g : T ⟶ S)
    (p : V ⟶ X) (q : V ⟶ T) (p₀ : V' ⟶ U) (q₀ : V' ⟶ T)
    (h : p ≫ f = q ≫ g) (h₀ : p₀ ≫ f₀ = q₀ ≫ g)
    (e : U ⟶ X) (r : V' ⟶ V)
    (he : e ≫ f = f₀) (hp : r ≫ p = p₀ ≫ e) (hq : r ≫ q = q₀)
    (adj : ∀ {A B : Scheme.{u}} (s : A ⟶ B),
      derivedPullback s ⊣ schemeDerivedDirectImage s)
    (c : ∀ {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C),
      derivedPullback t ⋙ derivedPullback s ≅ derivedPullback (s ≫ t))
    (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
        Functor.associator (derivedPullback g) (derivedPullback f)
            (derivedPullback h) ≪≫
          Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
              (Category.assoc h f g)))
    (bc : ∀ {A B C D : Scheme.{u}} (l : A ⟶ C) (m : B ⟶ D)
      (v : D ⟶ C) (s : B ⟶ A) (hs : s ≫ l = m ≫ v)
      (F : schemeDerivedCategory A),
      schemeDerivedBaseChangeMap l m v s hs F =
        (adj m).homEquiv _ _
          ((c m v).hom.app ((schemeDerivedDirectImage l).obj F) ≫
            eqToHom (congrArg (fun z ↦
              (derivedPullback z).obj ((schemeDerivedDirectImage l).obj F)) hs.symm) ≫
            (c s l).inv.app ((schemeDerivedDirectImage l).obj F) ≫
            (derivedPullback s).map ((adj l).counit.app F))) :
    let ce := c e f ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) he)
    let cr := c r q ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) hq)
    let δe := conjugateIsoEquiv (adj f₀) ((adj f).comp (adj e)) ce
    let δr := conjugateIsoEquiv (adj q₀) ((adj q).comp (adj r)) cr
    ∀ E : schemeDerivedCategory X,
      schemeDerivedBaseChangeMap f q g p h E ≫
        (schemeDerivedDirectImage q).map ((adj r).unit.app ((derivedPullback p).obj E)) ≫
        δr.inv.app ((derivedPullback r).obj ((derivedPullback p).obj E)) ≫
        (schemeDerivedDirectImage q₀).map
          ((c r p).hom.app E ≫
            eqToHom (congrArg (fun s ↦ (derivedPullback s).obj E) hp) ≫
            (c p₀ e).inv.app E) =
      (derivedPullback g).map
          ((schemeDerivedDirectImage f).map ((adj e).unit.app E) ≫
            δe.inv.app ((derivedPullback e).obj E)) ≫
        schemeDerivedBaseChangeMap f₀ q₀ g p₀ h₀ ((derivedPullback e).obj E) := by
  classical
  intro ce cr δe δr E
  subst f₀
  subst q₀
  let cf := c e f
  let cf' := c r q
  let ch : derivedPullback p ⋙ derivedPullback r ≅
      derivedPullback e ⋙ derivedPullback p₀ :=
    c r p ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) hp) ≪≫ (c p₀ e).symm
  let b : derivedPullback g ⋙ derivedPullback q ≅
      derivedPullback f ⋙ derivedPullback p :=
    c q g ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) h.symm) ≪≫ (c p f).symm
  let b₀ : derivedPullback g ⋙ derivedPullback (r ≫ q) ≅
      derivedPullback (e ≫ f) ⋙ derivedPullback p₀ :=
    c (r ≫ q) g ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) h₀.symm) ≪≫
      (c p₀ (e ≫ f)).symm
  have hb : ∀ Z : schemeDerivedCategory S,
      (derivedPullback r).map (b.hom.app Z) ≫
        ch.hom.app ((derivedPullback f).obj Z) ≫
        (derivedPullback p₀).map (cf.hom.app Z) =
      cf'.hom.app ((derivedPullback g).obj Z) ≫ b₀.hom.app Z := by
    intro Z
    simpa only [b, b₀, ch, cf, cf', Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Iso.symm_hom, Category.assoc] using
      pullback_source_square c hc f q g p h e r p₀ hp.symm h₀ Z
  let d := (schemeDerivedDirectImage f).map ((adj e).unit.app E) ≫
    (conjugateIsoEquiv (adj (e ≫ f)) ((adj f).comp (adj e)) cf).inv.app
      ((derivedPullback e).obj E)
  let d' := (schemeDerivedDirectImage q).map ((adj r).unit.app ((derivedPullback p).obj E)) ≫
    (conjugateIsoEquiv (adj (r ≫ q)) ((adj q).comp (adj r)) cf').inv.app
      ((derivedPullback r).obj ((derivedPullback p).obj E))
  have core := source_mate_transport (adj f) (adj q) (adj (e ≫ f)) (adj (r ≫ q))
    cf cf' ch b b₀ hb E ((derivedPullback p).obj E) (𝟙 _) d d'
    (source_transport_counit (adj f) (adj e) (adj (e ≫ f)) cf E)
    (source_transport_counit (adj q) (adj r) (adj (r ≫ q)) cf'
      ((derivedPullback p).obj E))
  have bc₁ : schemeDerivedBaseChangeMap f q g p h E =
      (adj q).homEquiv _ _ (b.hom.app ((schemeDerivedDirectImage f).obj E) ≫
        (derivedPullback p).map ((adj f).counit.app E)) := by
    simp only [bc, b, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  have bc₂ : schemeDerivedBaseChangeMap (e ≫ f) (r ≫ q) g p₀ h₀
        ((derivedPullback e).obj E) =
      (adj (r ≫ q)).homEquiv _ _
        (b₀.hom.app ((schemeDerivedDirectImage (e ≫ f)).obj ((derivedPullback e).obj E)) ≫
          (derivedPullback p₀).map ((adj (e ≫ f)).counit.app ((derivedPullback e).obj E))) := by
    simp only [bc, b₀, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  rw [← bc₁, ← bc₂] at core
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at core
  have hh := congrArg (fun z ↦ z ≫ (schemeDerivedDirectImage (r ≫ q)).map
    (ch.hom.app E)) core
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  simp only [ce, cr, δe, δr, eqToIso_refl, Iso.trans_refl]
  simpa only [d, d', ch, cf, cf', Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Iso.symm_hom, Category.assoc] using hh


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def qcUnitComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X U S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (f₀ : U ⟶ S) (e : U ⟶ X)
    (adj : derivedPullback e ⊣ schemeDerivedDirectImage e)
    (δ : schemeDerivedDirectImage f₀ ≅ schemeDerivedDirectImage e ⋙
      schemeDerivedDirectImage f) :
    qcDirectImage f ⟶ qcPullback e ⋙ qcDirectImage f₀ :=
  { app := fun E ↦ ObjectProperty.homMk
      ((schemeDerivedDirectImage f).map (adj.unit.app E.obj) ≫
        δ.inv.app ((derivedPullback e).obj E.obj))
    naturality := fun E F a ↦ by
      ext
      change (schemeDerivedDirectImage f).map a.hom ≫
          ((schemeDerivedDirectImage f).map (adj.unit.app F.obj) ≫
            δ.inv.app ((derivedPullback e).obj F.obj)) =
        ((schemeDerivedDirectImage f).map (adj.unit.app E.obj) ≫
          δ.inv.app ((derivedPullback e).obj E.obj)) ≫
            (schemeDerivedDirectImage f₀).map ((derivedPullback e).map a.hom)
      rw [← Functor.map_comp_assoc]
      erw [adj.unit.naturality a.hom]
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      exact congrArg (fun z ↦ (schemeDerivedDirectImage f).map (adj.unit.app E.obj) ≫ z)
        (δ.inv.naturality ((derivedPullback e).map a.hom)) }


set_option maxHeartbeats 200000 in
-- The explicit mate calculation needs a larger elaboration budget.
/-- Transport of the inverse ordinary base-change square along a source isomorphism.
The component formulas determine all three comparisons uniquely.
This theorem has no exceptional right adjoints and no second mates.
Source: Stacks Project, Tag 0ATR, composite adjunction calculation; Tag 0D5S.
(blueprint: lem-sc-scheme-iso-inverse-base-change-transport)

Proof: The pinned pullback adjunction of each source isomorphism is an equivalence:
pullback along its inverse is an inverse functor by the canonical composition and
identity comparisons. Thus its unit, and hence the explicitly constructed unit
comparison q, is invertible. Transpose ordinary base change under the pinned
pullback/direct-image adjunctions. Apply derived base-change pasting to r and use
hr₂ for the upper direct-image comparison. Apply pullback composition to the other
projection and use hr₁ and he. The associativity law for the fixed composition
comparisons identifies these transposes. Injectivity of the Hom equivalences gives
the ordinary-square equation with the specified k, q and σ. Invert the two ordinary
base-change transformations, which are isomorphisms by hβ and hβf; cancel them on
the two sides. Naturality moves k and q through the composites and gives exactly
the displayed inverse-square equation. The component identity for q is recorded
after two arbitrary postcompositions, using associativity; identity arrows recover
the unpostcomposed component. It holds for every quasi-coherent object,
including the zero object, and on empty schemes: only naturality, composition and
triangle identities are used. Restriction to quasi-coherent objects is legitimate
by pullback and qcqs direct-image preservation; full faithfulness gives the same
equality in the full subcategories. -/
theorem schemeIso_inverseBaseChange_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f') (g : T ⟶ S)
    (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f' g)
    [IsIso r]
    [QuasiSeparatedSpace (pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (pullback f' g : Scheme.{u})]
    (hβ : ∀ E : schemeDerivedQCohCategory U,
      IsIso (schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
        (pullback.fst f' g) pullback.condition E.obj))
    (hβf : ∀ E : schemeDerivedQCohCategory P,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj)) :
    let adj := fun {X Y : Scheme.{u}} (v : X ⟶ Y) ↦
      Classical.choose (exists_schemeDerivedAdjunction v
        (hAdd := (Classical.choose exists_derivedPullbackComposition) v)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) v)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) v))
    let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
    let ce := comp e.hom f ≪≫ eqToIso (congrArg (fun v ↦ derivedPullback v) he)
    let cr := comp (asIso r).hom (pullback.snd f g) ≪≫
      eqToIso (congrArg (fun v ↦ derivedPullback v) hr₂)
    let δe := conjugateIsoEquiv (adj f') ((adj f).comp (adj e.hom)) ce
    let δr := conjugateIsoEquiv (adj (pullback.snd f' g))
      ((adj (pullback.snd f g)).comp (adj (asIso r).hom)) cr
    ∃ (k : qcDirectImage f ⟶ qcPullback e.hom ⋙ qcDirectImage f')
      (q : qcDirectImage (pullback.snd f g) ⟶
        qcPullback r ⋙ qcDirectImage (pullback.snd f' g))
      (σ : qcPullback (pullback.fst f g) ⋙ qcPullback r ≅
        qcPullback e.hom ⋙ qcPullback (pullback.fst f' g)),
      IsIso q ∧
      (∀ E : schemeDerivedQCohCategory P,
        q.app ((qcPullback (pullback.fst f g)).obj E) ≫
          (qcDirectImage (pullback.snd f' g)).map (σ.hom.app E) ≫
          (qcInverseBaseChange f' g hβ).app ((qcPullback e.hom).obj E) =
        (qcInverseBaseChange f g hβf).app E ≫ (qcPullback g).map (k.app E)) ∧
      (∀ E : schemeDerivedQCohCategory P,
        (k.app E).hom = (schemeDerivedDirectImage f).map
          ((adj e.hom).unit.app E.obj) ≫
            δe.inv.app ((derivedPullback e.hom).obj E.obj)) ∧
      (∀ (E : schemeDerivedQCohCategory (pullback f g))
          (A B : schemeDerivedCategory T)
          (t : ((qcPullback r ⋙ qcDirectImage (pullback.snd f' g)).obj E).obj ⟶ A)
          (v : A ⟶ B),
        (q.app E).hom ≫ t ≫ v =
          (schemeDerivedDirectImage (pullback.snd f g)).map
            ((adj (asIso r).hom).unit.app E.obj) ≫
          δr.inv.app ((derivedPullback (asIso r).hom).obj E.obj) ≫ t ≫ v) ∧
      (∀ E : schemeDerivedQCohCategory P,
        (σ.hom.app E).hom =
          (comp r (pullback.fst f g)).hom.app E.obj ≫
            eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hr₁) ≫
            (comp (pullback.fst f' g) e.hom).inv.app E.obj) := by
  classical
  intro adj comp ce cr δe δr
  let k := qcUnitComparison f f' e.hom (adj e.hom) δe
  let q := qcUnitComparison (pullback.snd f g) (pullback.snd f' g) r (adj r) δr
  let σ₀ : derivedPullback (pullback.fst f g) ⋙ derivedPullback r ≅
      derivedPullback e.hom ⋙ derivedPullback (pullback.fst f' g) :=
    comp r (pullback.fst f g) ≪≫
      eqToIso (congrArg (fun v ↦ derivedPullback v) hr₁) ≪≫
        (comp (pullback.fst f' g) e.hom).symm
  let σ : qcPullback (pullback.fst f g) ⋙ qcPullback r ≅
      qcPullback e.hom ⋙ qcPullback (pullback.fst f' g) :=
    NatIso.ofComponents (fun E ↦ (schemeDerivedQCohProperty (pullback f' g)).isoMk
      (σ₀.app E.obj)) (by
        intro E F a
        ext
        exact σ₀.hom.naturality a.hom)
  obtain ⟨i, _, _, hc⟩ :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2
  have bc {A B C D : Scheme.{u}} (l : A ⟶ C) (m : B ⟶ D)
      (v : D ⟶ C) (s : B ⟶ A) (hs : s ≫ l = m ≫ v)
      (F : schemeDerivedCategory A) :
      schemeDerivedBaseChangeMap l m v s hs F =
        (adj m).homEquiv _ _
          ((comp m v).hom.app ((schemeDerivedDirectImage l).obj F) ≫
            eqToHom (congrArg (fun z ↦
              (derivedPullback z).obj ((schemeDerivedDirectImage l).obj F)) hs.symm) ≫
            (comp s l).inv.app ((schemeDerivedDirectImage l).obj F) ≫
            (derivedPullback s).map ((adj l).counit.app F)) := by rfl
  let er := asIso r
  let b : derivedPullback er.hom ⋙ derivedPullback er.inv ≅ 𝟭 _ :=
    comp er.inv er.hom ≪≫ eqToIso
      (congrArg (fun v ↦ derivedPullback v) er.inv_hom_id) ≪≫ i (pullback f g)
  let d : derivedPullback er.inv ⋙ derivedPullback er.hom ≅ 𝟭 _ :=
    comp er.hom er.inv ≪≫ eqToIso
      (congrArg (fun v ↦ derivedPullback v) er.hom_inv_id) ≪≫ i (pullback f' g)
  have : (derivedPullback er.inv).Faithful := Functor.Faithful.of_comp_iso d
  have : (derivedPullback r).Faithful := Functor.Faithful.of_comp_iso b
  have : (derivedPullback r).Full := Functor.Full.of_comp_faithful_iso b
  have : IsIso (adj r).unit := inferInstance
  have hq : IsIso q := by
    have : ∀ E, IsIso (q.app E) := fun E ↦ by
      have : IsIso ((q.app E).hom) := by
        change IsIso ((schemeDerivedDirectImage (pullback.snd f g)).map
          ((adj r).unit.app E.obj) ≫ δr.inv.app ((derivedPullback r).obj E.obj))
        set_option backward.isDefEq.respectTransparency false in
          infer_instance
      exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
        (schemeDerivedQCohProperty T).fullyFaithfulι _ _ (q.app E) this
    exact NatIso.isIso_of_isIso_app q
  refine ⟨k, q, σ, hq, ?_, ?_, ?_, ?_⟩
  · intro E
    have ordinary := ordinary_source_transport f f' g
      (pullback.fst f g) (pullback.snd f g)
      (pullback.fst f' g) (pullback.snd f' g)
      pullback.condition pullback.condition e.hom r he hr₁ hr₂ adj comp hc bc E.obj
    have heq : (qcBaseChange f g).app E ≫
        q.app ((qcPullback (pullback.fst f g)).obj E) ≫
        (qcDirectImage (pullback.snd f' g)).map (σ.hom.app E) =
      (qcPullback g).map (k.app E) ≫
        (qcBaseChange f' g).app ((qcPullback e.hom).obj E) := by
      ext
      change schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition E.obj ≫
        ((schemeDerivedDirectImage (pullback.snd f g)).map
          ((adj r).unit.app ((derivedPullback (pullback.fst f g)).obj E.obj)) ≫
          δr.inv.app ((derivedPullback r).obj
            ((derivedPullback (pullback.fst f g)).obj E.obj))) ≫
        (schemeDerivedDirectImage (pullback.snd f' g)).map (σ₀.hom.app E.obj) =
        (derivedPullback g).map
          ((schemeDerivedDirectImage f).map ((adj e.hom).unit.app E.obj) ≫
            δe.inv.app ((derivedPullback e.hom).obj E.obj)) ≫
        schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
          (pullback.fst f' g) pullback.condition ((derivedPullback e.hom).obj E.obj)
      set_option backward.isDefEq.respectTransparency false in
       set_option backward.isDefEq.respectTransparency.types false in
        simpa only [σ₀, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
        Iso.symm_hom, Category.assoc, ce, cr, δe, δr, asIso_hom] using ordinary
    have hb : ∀ F, IsIso ((qcBaseChange f g).app F) := fun F ↦
      @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
        (schemeDerivedQCohProperty T).fullyFaithfulι _ _ ((qcBaseChange f g).app F) (hβf F)
    have hb' : ∀ F, IsIso ((qcBaseChange f' g).app F) := fun F ↦
      @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
        (schemeDerivedQCohProperty T).fullyFaithfulι _ _ ((qcBaseChange f' g).app F) (hβ F)
    have : IsIso (qcBaseChange f g) := NatIso.isIso_of_isIso_app _
    have : IsIso (qcBaseChange f' g) := NatIso.isIso_of_isIso_app _
    change q.app _ ≫ (qcDirectImage (pullback.snd f' g)).map (σ.hom.app E) ≫
      (inv (qcBaseChange f' g)).app _ =
      (inv (qcBaseChange f g)).app E ≫ (qcPullback g).map (k.app E)
    apply (cancel_epi ((qcBaseChange f g).app E)).mp
    simpa only [Category.assoc, NatIso.isIso_inv_app,
      IsIso.hom_inv_id, IsIso.hom_inv_id_assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun z ↦ z ≫ (inv (qcBaseChange f' g)).app
        ((qcPullback e.hom).obj E)) heq
  · intro E
    rfl
  · intro E A B t v
    exact Category.assoc _ _ _
  · intro E
    simp only [σ, σ₀, NatIso.ofComponents_hom_app, ObjectProperty.isoMk,
      ObjectProperty.homMk, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Iso.symm_hom]


end
end AlgebraicGeometry
