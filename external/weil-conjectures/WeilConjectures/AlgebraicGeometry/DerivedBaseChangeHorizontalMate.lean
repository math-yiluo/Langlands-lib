/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
namespace AlgebraicGeometry

private theorem horizontal_mates
    {C B D F T U : Type*}
    [Category C] [Category B] [Category D] [Category F] [Category T] [Category U]
    {L : C ⥤ D} {R : D ⥤ C} {M : B ⥤ F} {Q : F ⥤ B}
    {V : D ⥤ T} {W : T ⥤ D} {V' : F ⥤ U} {W' : U ⥤ F}
    {L₀ : C ⥤ T} {R₀ : T ⥤ C} {M₀ : B ⥤ U} {Q₀ : U ⥤ B}
    {K : C ⥤ B} {H : D ⥤ F} {J : T ⥤ U}
    (a : L ⊣ R) (b : M ⊣ Q) (v : V ⊣ W) (v' : V' ⊣ W')
    (a₀ : L₀ ⊣ R₀) (b₀ : M₀ ⊣ Q₀)
    (cf : L ⋙ V ≅ L₀) (cf' : M ⋙ V' ≅ M₀)
    (q : K ⋙ M ≅ L ⋙ H) (s : H ⋙ V' ≅ V ⋙ J)
    (q₀ : K ⋙ M₀ ≅ L₀ ⋙ J)
    (hq : ∀ Z : C,
      V'.map (q.hom.app Z) ≫ s.hom.app (L.obj Z) ≫ J.map (cf.hom.app Z) =
        cf'.hom.app (K.obj Z) ≫ q₀.hom.app Z)
    (E : T) :
    let k := ((a.comp v).ofNatIsoLeft cf).rightAdjointUniq a₀
    let k' := ((b.comp v').ofNatIsoLeft cf').rightAdjointUniq b₀
    b.homEquiv _ _ (q.hom.app (R.obj (W.obj E)) ≫
        H.map (a.counit.app (W.obj E))) ≫
        Q.map (v'.homEquiv _ _ (s.hom.app (W.obj E) ≫ J.map (v.counit.app E))) =
      K.map (k.hom.app E) ≫
        b₀.homEquiv _ _ (q₀.hom.app (R₀.obj E) ≫ J.map (a₀.counit.app E)) ≫
        k'.inv.app (J.obj E) := by
  intro k k'
  let z : M.obj (K.obj (R.obj (W.obj E))) ⟶ H.obj (W.obj E) :=
    q.hom.app (R.obj (W.obj E)) ≫ H.map (a.counit.app (W.obj E))
  let y : V'.obj (H.obj (W.obj E)) ⟶ J.obj E := s.hom.app (W.obj E) ≫ J.map (v.counit.app E)
  let z₀ : M₀.obj (K.obj (R₀.obj E)) ⟶ J.obj E := q₀.hom.app (R₀.obj E) ≫ J.map (a₀.counit.app E)
  have hd : L₀.map (k.hom.app E) ≫ a₀.counit.app E =
      cf.inv.app (R.obj (W.obj E)) ≫
        V.map (a.counit.app (W.obj E)) ≫ v.counit.app E := by
    simpa only [k, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_counit_app, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using
      Adjunction.rightAdjointUniq_hom_app_counit
        ((a.comp v).ofNatIsoLeft cf) a₀ E
  have hd' : M₀.map (k'.hom.app (J.obj E)) ≫ b₀.counit.app (J.obj E) =
      cf'.inv.app (Q.obj (W'.obj (J.obj E))) ≫
        V'.map (b.counit.app (W'.obj (J.obj E))) ≫ v'.counit.app (J.obj E) := by
    simpa only [k', Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_counit_app, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using
      Adjunction.rightAdjointUniq_hom_app_counit
        ((b.comp v').ofNatIsoLeft cf') b₀ (J.obj E)
  apply (cancel_mono (k'.hom.app (J.obj E))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  apply (b₀.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  suffices M₀.map ((b.homEquiv _ _ z ≫ Q.map (v'.homEquiv _ _ y)) ≫
      k'.hom.app (J.obj E)) ≫ b₀.counit.app (J.obj E) =
    M₀.map (K.map (k.hom.app E) ≫ b₀.homEquiv _ _ z₀) ≫
      b₀.counit.app (J.obj E) by
    simpa only [z, y, z₀, Functor.id_obj, Category.assoc] using this
  rw [M₀.map_comp, Category.assoc, hd']
  erw [reassoc_of% cf'.inv.naturality (b.homEquiv _ _ z ≫ Q.map (v'.homEquiv _ _ y))]
  have hb : M.map (b.homEquiv _ _ z ≫ Q.map (v'.homEquiv _ _ y)) ≫
      b.counit.app (W'.obj (J.obj E)) = z ≫ v'.homEquiv _ _ y := by
    rw [M.map_comp, Category.assoc]
    erw [b.counit.naturality (v'.homEquiv _ _ y)]
    rw [← Category.assoc]
    exact congrArg (fun x ↦ x ≫ v'.homEquiv _ _ y)
      ((b.homEquiv _ _).symm_apply_apply z)
  change cf'.inv.app (K.obj (R.obj (W.obj E))) ≫
      V'.map (M.map (b.homEquiv _ _ z ≫ Q.map (v'.homEquiv _ _ y))) ≫
      V'.map (b.counit.app (W'.obj (J.obj E))) ≫ _ = _
  rw [← V'.map_comp_assoc, hb, V'.map_comp, Category.assoc]
  have hv : V'.map (v'.homEquiv _ _ y) ≫ v'.counit.app (J.obj E) = y :=
    ((v'.homEquiv _ _).symm_apply_apply y)
  rw [hv, M₀.map_comp, Category.assoc]
  have hb₀ : M₀.map (b₀.homEquiv _ _ z₀) ≫ b₀.counit.app (J.obj E) = z₀ :=
    ((b₀.homEquiv _ _).symm_apply_apply z₀)
  rw [hb₀]
  dsimp only [z₀]
  erw [reassoc_of% q₀.hom.naturality (k.hom.app E)]
  change _ = q₀.hom.app (R.obj (W.obj E)) ≫ J.map (L₀.map (k.hom.app E)) ≫
    J.map (a₀.counit.app E)
  rw [← J.map_comp, hd, J.map_comp, J.map_comp]
  dsimp only [z, y]
  simp only [V'.map_comp, Category.assoc]
  erw [reassoc_of% s.hom.naturality (a.counit.app (W.obj E))]
  have hc : cf'.inv.app (K.obj (R.obj (W.obj E))) ≫
      V'.map (q.hom.app (R.obj (W.obj E))) ≫
      s.hom.app (L.obj (R.obj (W.obj E))) =
    q₀.hom.app (R.obj (W.obj E)) ≫ J.map (cf.inv.app (R.obj (W.obj E))) := by
    have hh := congrArg (fun x ↦ cf'.inv.app (K.obj (R.obj (W.obj E))) ≫ x ≫
      J.map (cf.inv.app (R.obj (W.obj E)))) (hq (R.obj (W.obj E)))
    simp only [Category.assoc, ← J.map_comp, Iso.hom_inv_id_app,
      Iso.inv_hom_id_app_assoc] at hh
    erw [J.map_id] at hh
    dsimp only [Functor.comp_obj] at hh
    simpa only [Category.comp_id] using hh
  exact (reassoc_of% hc) _

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

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem baseChange_eq
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (E : schemeDerivedCategory X) :
    schemeDerivedBaseChangeMap f f' g g' h E =
      (relativeMVAdj f').homEquiv _ _
        ((relativeMVComp f' g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
          eqToHom (congrArg (fun k ↦
            (derivedPullback k).obj ((schemeDerivedDirectImage f).obj E)) h.symm) ≫
          (relativeMVComp g' f).inv.app ((schemeDerivedDirectImage f).obj E) ≫
          (derivedPullback g').map ((relativeMVAdj f).counit.app E)) := by
  rfl

/-- The mate calculation before the final relative composition comparison.
Source: Stacks Project, Cohomology, Tags 08HY and 0D5S.
(blueprint: new-lem-pc-derived-base-change-horizontal-mate).
The proof expands each base-change map as the transpose of the corresponding
counit, uses naturality and the triangle identity, and then applies associativity
of the pinned pullback comparison. This is the intermediate mate identity used
by `schemeDerivedBaseChange_horizontal`; it is stated before postcomposition by
the canonical direct-image composition isomorphism. -/
theorem schemeDerivedBaseChange_horizontal_mate
    {A X S A' X' S' : Scheme.{u}}
    (j : A ⟶ X) (f : X ⟶ S) (j' : A' ⟶ X') (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (v : A' ⟶ A)
    (h : g' ≫ f = f' ≫ g) (hj : v ≫ j = j' ≫ g')
    (E : schemeDerivedCategory A) :
    schemeDerivedBaseChangeMap f f' g g' h ((schemeDerivedDirectImage j).obj E) ≫
        (schemeDerivedDirectImage f').map
          (schemeDerivedBaseChangeMap j j' g' v hj E) =
      (derivedPullback g).map ((relativeMVImageComp j f).hom.app E) ≫
        schemeDerivedBaseChangeMap (j ≫ f) (j' ≫ f') g v
          (by rw [← Category.assoc, hj, Category.assoc, h, ← Category.assoc]) E ≫
        (relativeMVImageComp j' f').inv.app ((derivedPullback v).obj E) := by
  classical
  let c := fun {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z) ↦
    relativeMVComp k l
  let a := fun {P Q : Scheme.{u}} (k : P ⟶ Q) ↦ relativeMVAdj k
  let square := fun {P Q P' Q' : Scheme.{u}}
      (r : P ⟶ Q) (r' : P' ⟶ Q') (s : Q' ⟶ Q) (t : P' ⟶ P)
      (e : t ≫ r = r' ≫ s) ↦
    c r' s ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm) ≪≫ (c t r).symm
  let ho : v ≫ (j ≫ f) = (j' ≫ f') ≫ g := by
    rw [← Category.assoc, hj, Category.assoc, h, ← Category.assoc]
  have assoc := fun {P Q Z T : Scheme.{u}}
      (r : P ⟶ Q) (s : Q ⟶ Z) (t : Z ⟶ T) ↦
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).2.choose_spec.2.2 r s t
  have hq : ∀ Z : schemeDerivedCategory S,
      (derivedPullback j').map ((square f f' g g' h).hom.app Z) ≫
        (square j j' g' v hj).hom.app ((derivedPullback f).obj Z) ≫
        (derivedPullback v).map ((c j f).hom.app Z) =
      (c j' f').hom.app ((derivedPullback g).obj Z) ≫
        (square (j ≫ f) (j' ≫ f') g v ho).hom.app Z := by
    intro Z
    simpa only [square, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc] using
      pullback_source_square c assoc f f' g g' h j j' v hj ho Z
  have hm := horizontal_mates (a f) (a f') (a j) (a j')
    (a (j ≫ f)) (a (j' ≫ f')) (c j f) (c j' f')
    (square f f' g g' h) (square j j' g' v hj)
    (square (j ≫ f) (j' ≫ f') g v ho) hq E
  rw [baseChange_eq, baseChange_eq, baseChange_eq]
  simpa only [a, c, square, relativeMVImageComp, Functor.id_obj, Functor.comp_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Category.assoc] using hm

end AlgebraicGeometry
