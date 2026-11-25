/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Source-coordinate naturality of the derived comparison

Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-derived-base-change-source-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

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
private theorem mate_naturality
    {C B D F : Type*} [Category C] [Category B] [Category D] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {M : B ⥤ F} {Q : F ⥤ B}
    {K : C ⥤ B} {H : D ⥤ F}
    (a : L ⊣ R) (b : M ⊣ Q) (q : K ⋙ M ≅ L ⋙ H)
    {E N : D} (s : E ⟶ N) :
    K.map (R.map s) ≫
        b.homEquiv _ _ (q.hom.app (R.obj N) ≫ H.map (a.counit.app N)) =
      b.homEquiv _ _ (q.hom.app (R.obj E) ≫ H.map (a.counit.app E)) ≫
        Q.map (H.map s) := by
  rw [← b.homEquiv_naturality_left, ← b.homEquiv_naturality_right]
  apply congrArg (b.homEquiv _ _)
  erw [reassoc_of% q.hom.naturality (R.map s)]
  change q.hom.app (R.obj E) ≫ H.map (L.map (R.map s)) ≫ H.map (a.counit.app N) = _
  rw [← H.map_comp]
  erw [a.counit.naturality s]
  simp only [Functor.id_map, H.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Changing both source coordinates, and transporting the coefficient arrow, conjugates
its derived comparison by isomorphisms. This statement concerns arbitrary commutative
squares, not open restrictions or the invertibility of the comparison.
Source: Stacks Project, cohomology.tex, Tag 08HY (counit definition of base change)
and Tag 0D5S (composition of derived pullback).
(blueprint: lem-pc-derived-base-change-source-iso).

Proof: Use the composition comparisons c selected by exists_derivedPullbackComposition
and the adjunctions pinned to their derived counits by exists_schemeDerivedAdjunction.
For a scheme isomorphism e, the comparisons for e.hom followed by e.inv, and conversely,
together with the identity comparison, exhibit pullback as an equivalence. Its pinned
adjunction therefore has invertible unit and counit. The right-adjoint mate of c e.hom f
identifies R(e.hom f) with R(e.hom) followed by Rf. Insert the unit for e.hom to identify
Rf E with R(e.hom f) L(e.hom) E, and then apply the image of alpha. Applying Lg gives
the source isomorphism a. Perform the same construction for e' and beta to obtain b.
Transpose the claimed equation under the adjunction for e'.hom followed by f'.
Naturality of its counit identifies the right-hand transpose with the pullback of the
original transpose, after the comparison c for the source-coordinate square. The
associativity law for c identifies its square comparison with that for t; equality
transports agree by ht and proof irrelevance. Substitute hphi to identify the final
coefficient factors. The triangle identities cancel the units inserted in a and b.
The Hom equivalence is injective, proving the equation. All these identities apply to
zero coefficients, identity coordinates and empty schemes; no cartesian, affine or
quasi-coherent hypothesis is used. -/
theorem exists_derivedBaseChange_source_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' T T' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (e : T ≅ X) (e' : T' ≅ X') (t : T' ⟶ T)
    (ht : t ≫ e.hom = e'.hom ≫ g')
    (h0 : t ≫ (e.hom ≫ f) = (e'.hom ≫ f') ≫ g)
    (E : schemeDerivedCategory X) (E' : schemeDerivedCategory X')
    (N : schemeDerivedCategory T) (N' : schemeDerivedCategory T')
    (phi : (derivedPullback g').obj E ⟶ E')
    (phi0 : (derivedPullback t).obj N ⟶ N')
    (alpha : (derivedPullback e.hom).obj E ≅ N)
    (beta : (derivedPullback e'.hom).obj E' ≅ N')
    (hphi :
      (derivedPullback t).map alpha.hom ≫ phi0 =
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))) t e.hom).hom.app E ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj E) ht) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))) e'.hom g').inv.app E ≫
        (derivedPullback e'.hom).map phi ≫ beta.hom) :
    ∃ (a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
          (derivedPullback g).obj ((schemeDerivedDirectImage (e.hom ≫ f)).obj N))
      (b : (schemeDerivedDirectImage f').obj E' ≅
          (schemeDerivedDirectImage (e'.hom ≫ f')).obj N'),
      (schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map phi) ≫ b.hom =
      a.hom ≫ (schemeDerivedBaseChangeMap (e.hom ≫ f) (e'.hom ≫ f') g t h0 N ≫
        (schemeDerivedDirectImage (e'.hom ≫ f')).map phi0) := by
  classical
  let c : ∀ {A B C : Scheme.{u}} (r : A ⟶ B) (s : B ⟶ C),
      derivedPullback s ⋙ derivedPullback r ≅ derivedPullback (r ≫ s) :=
    @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
  let adj : ∀ {A B : Scheme.{u}} (s : A ⟶ B),
      derivedPullback s ⊣ schemeDerivedDirectImage s := fun s ↦
    Classical.choose (exists_schemeDerivedAdjunction s
      (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) s))
  obtain ⟨_, i, _, _, hc⟩ := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))
  have unitIso {A B : Scheme.{u}} (v : A ≅ B) : IsIso (adj v.hom).unit := by
    let b : derivedPullback v.hom ⋙ derivedPullback v.inv ≅ 𝟭 _ :=
      c v.inv v.hom ≪≫
        eqToIso (congrArg (fun s ↦ derivedPullback s) v.inv_hom_id) ≪≫ i B
    let d : derivedPullback v.inv ⋙ derivedPullback v.hom ≅ 𝟭 _ :=
      c v.hom v.inv ≪≫
        eqToIso (congrArg (fun s ↦ derivedPullback s) v.hom_inv_id) ≪≫ i A
    have : (derivedPullback v.inv).Faithful := Functor.Faithful.of_comp_iso d
    have : (derivedPullback v.hom).Faithful := Functor.Faithful.of_comp_iso b
    have : (derivedPullback v.hom).Full := Functor.Full.of_comp_faithful_iso b
    infer_instance
  have : IsIso (adj e.hom).unit := unitIso e
  have : IsIso (adj e'.hom).unit := unitIso e'
  let k := conjugateIsoEquiv (adj (e.hom ≫ f)) ((adj f).comp (adj e.hom)) (c e.hom f)
  let k' := conjugateIsoEquiv (adj (e'.hom ≫ f'))
    ((adj f').comp (adj e'.hom)) (c e'.hom f')
  let d := (schemeDerivedDirectImage f).mapIso ((asIso (adj e.hom).unit).app E) ≪≫
    k.symm.app ((derivedPullback e.hom).obj E)
  let d' := (schemeDerivedDirectImage f').mapIso ((asIso (adj e'.hom).unit).app E') ≪≫
    k'.symm.app ((derivedPullback e'.hom).obj E')
  let q : derivedPullback g ⋙ derivedPullback f' ≅
      derivedPullback f ⋙ derivedPullback g' :=
    c f' g ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) h.symm) ≪≫ (c g' f).symm
  let q₀ : derivedPullback g ⋙ derivedPullback (e'.hom ≫ f') ≅
      derivedPullback (e.hom ≫ f) ⋙ derivedPullback t :=
    c (e'.hom ≫ f') g ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) h0.symm) ≪≫
      (c t (e.hom ≫ f)).symm
  let ch : derivedPullback g' ⋙ derivedPullback e'.hom ≅
      derivedPullback e.hom ⋙ derivedPullback t :=
    c e'.hom g' ≪≫ eqToIso (congrArg (fun s ↦ derivedPullback s) ht.symm) ≪≫
      (c t e.hom).symm
  have hq : ∀ Z : schemeDerivedCategory S,
      (derivedPullback e'.hom).map (q.hom.app Z) ≫
        ch.hom.app ((derivedPullback f).obj Z) ≫
        (derivedPullback t).map ((c e.hom f).hom.app Z) =
      (c e'.hom f').hom.app ((derivedPullback g).obj Z) ≫ q₀.hom.app Z := by
    intro Z
    simpa only [q, q₀, ch, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Iso.symm_hom, Category.assoc] using
      pullback_source_square c hc f f' g g' h e.hom e'.hom t ht h0 Z
  have core := source_mate_transport (adj f) (adj f') (adj (e.hom ≫ f))
    (adj (e'.hom ≫ f')) (c e.hom f) (c e'.hom f') ch q q₀ hq E E' phi d.hom d'.hom
    (source_transport_counit (adj f) (adj e.hom) (adj (e.hom ≫ f)) (c e.hom f) E)
    (source_transport_counit (adj f') (adj e'.hom) (adj (e'.hom ≫ f')) (c e'.hom f') E')
  have bc {A B C D : Scheme.{u}} (l : A ⟶ C) (m : B ⟶ D)
      (r : D ⟶ C) (s : B ⟶ A) (hs : s ≫ l = m ≫ r)
      (F : schemeDerivedCategory A) :
      schemeDerivedBaseChangeMap l m r s hs F =
        (adj m).homEquiv _ _
          ((c m r).hom.app ((schemeDerivedDirectImage l).obj F) ≫
            eqToHom (congrArg (fun z ↦
              (derivedPullback z).obj ((schemeDerivedDirectImage l).obj F)) hs.symm) ≫
            (c s l).inv.app ((schemeDerivedDirectImage l).obj F) ≫
            (derivedPullback s).map ((adj l).counit.app F)) := by rfl
  have bcq (F : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h F =
        (adj f').homEquiv _ _ (q.hom.app ((schemeDerivedDirectImage f).obj F) ≫
          (derivedPullback g').map ((adj f).counit.app F)) := by
    rw [bc]
    simp only [q, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  have bcq₀ (F : schemeDerivedCategory T) :
      schemeDerivedBaseChangeMap (e.hom ≫ f) (e'.hom ≫ f') g t h0 F =
        (adj (e'.hom ≫ f')).homEquiv _ _
          (q₀.hom.app ((schemeDerivedDirectImage (e.hom ≫ f)).obj F) ≫
            (derivedPullback t).map ((adj (e.hom ≫ f)).counit.app F)) := by
    rw [bc]
    simp only [q₀, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
  rw [← bcq, ← bcq₀] at core
  have natural := mate_naturality (adj (e.hom ≫ f)) (adj (e'.hom ≫ f')) q₀ alpha.hom
  rw [← bcq₀, ← bcq₀] at natural
  have coeff : (derivedPullback t).map alpha.hom ≫ phi0 =
      ch.inv.app E ≫ (derivedPullback e'.hom).map phi ≫ beta.hom := by
    simpa only [ch, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
      eqToIso.inv, eqToHom_app, Category.assoc] using hphi
  refine ⟨(derivedPullback g).mapIso
      (d ≪≫ (schemeDerivedDirectImage (e.hom ≫ f)).mapIso alpha),
    d' ≪≫ (schemeDerivedDirectImage (e'.hom ≫ f')).mapIso beta, ?_⟩
  simp only [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% core]
  have coeff' : (ch.inv.app E ≫ (derivedPullback e'.hom).map phi) ≫ beta.hom =
      (derivedPullback t).map alpha.hom ≫ phi0 := by
    simpa only [Category.assoc] using coeff.symm
  rw [← Functor.map_comp (schemeDerivedDirectImage (e'.hom ≫ f'))
    (ch.inv.app E ≫ (derivedPullback e'.hom).map phi) beta.hom, coeff']
  simp only [Functor.map_comp]
  rw [← reassoc_of% natural]

end AlgebraicGeometry
