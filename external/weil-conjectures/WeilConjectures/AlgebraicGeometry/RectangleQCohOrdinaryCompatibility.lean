/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangePasting
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting

/-! # Ordinary compatibility of the rectangle comparison lifts -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem cancel_pasting_comparison
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    (F : C ⥤ D) (H : D ⥤ A) (G : C ⥤ A) (d : G ≅ F ⋙ H)
    {M N : C} (v : M ≅ N) {Z : A}
    (outer : Z ⟶ G.obj N) (b : Z ⟶ H.obj (F.obj M))
    (past : outer ≫ d.hom.app N ≫ H.map (F.map v.inv) = b) :
    b ≫ d.inv.app M ≫ G.map v.hom = outer := by
  rw [← past]
  simp only [Category.assoc]
  rw [← Functor.comp_map, d.inv.naturality_assoc]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem upper_pasting_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y P S I : Scheme.{u}} (f : X ⟶ Y) (g : S ⟶ Y)
    (p : P ⟶ X) (q : P ⟶ S) (hs : p ≫ f = q ≫ g) (t : I ⟶ P)
    (p' : I ⟶ X) (q' : I ⟶ S) (hp : t ≫ p = p') (hq : t ≫ q = q')
    (hs' : p' ≫ f = q' ≫ g)
    (c : ∀ {A B C : Scheme.{u}} (r : A ⟶ B) (s : B ⟶ C),
      derivedPullback s ⋙ derivedPullback r ≅ derivedPullback (r ≫ s))
    (a : ∀ {A B : Scheme.{u}} (r : A ⟶ B),
      derivedPullback r ⊣ schemeDerivedDirectImage r)
    (past : ∀ E : schemeDerivedCategory X,
      schemeDerivedBaseChangeMap f (t ≫ q) g (t ≫ p)
          (by rw [Category.assoc, hs, Category.assoc]) E ≫
        (conjugateIsoEquiv (a (t ≫ q)) ((a q).comp (a t)) (c t q)).hom.app
          ((derivedPullback (t ≫ p)).obj E) ≫
        (schemeDerivedDirectImage q).map
          ((schemeDerivedDirectImage t).map ((c t p).inv.app E)) =
      schemeDerivedBaseChangeMap f q g p hs E ≫
        (schemeDerivedDirectImage q).map ((a t).unit.app ((derivedPullback p).obj E))) :
    let d := conjugateIsoEquiv (a q') ((a q).comp (a t))
      (c t q ≪≫ eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hq))
    ∀ E : schemeDerivedCategory X,
      schemeDerivedBaseChangeMap f q g p hs E ≫
        (schemeDerivedDirectImage q).map ((a t).unit.app ((derivedPullback p).obj E)) ≫
        d.inv.app ((derivedPullback t).obj ((derivedPullback p).obj E)) ≫
        (schemeDerivedDirectImage q').map
          ((c t p).hom.app E ≫
            eqToHom (congrArg (fun r ↦ (derivedPullback r).obj E) hp)) =
      schemeDerivedBaseChangeMap f q' g p' hs' E := by
  classical
  subst p'
  subst q'
  intro d E
  let d₀ := conjugateIsoEquiv (a (t ≫ q)) ((a q).comp (a t)) (c t q)
  have hd : d = d₀ := by
    simp only [d, d₀, eqToIso_refl, Iso.trans_refl]
  rw [hd]
  have past := past E
  change schemeDerivedBaseChangeMap f (t ≫ q) g (t ≫ p) hs' E ≫
      d₀.hom.app ((derivedPullback (t ≫ p)).obj E) ≫
      (schemeDerivedDirectImage q).map
        ((schemeDerivedDirectImage t).map ((c t p).inv.app E)) =
    schemeDerivedBaseChangeMap f q g p hs E ≫
      (schemeDerivedDirectImage q).map ((a t).unit.app ((derivedPullback p).obj E))
    at past
  simp only [eqToHom_refl, Category.comp_id]
  simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj] using
    cancel_pasting_comparison
    (schemeDerivedDirectImage t) (schemeDerivedDirectImage q)
    (schemeDerivedDirectImage (t ≫ q)) d₀ ((c t p).app E)
    (schemeDerivedBaseChangeMap f (t ≫ q) g (t ≫ p) hs' E)
    (schemeDerivedBaseChangeMap f q g p hs E ≫
      (schemeDerivedDirectImage q).map ((a t).unit.app ((derivedPullback p).obj E))) past


/-- Ordinary base-change compatibility for the canonical comparison lifts.
Source: Stacks Project, Tag 0ATM, and Tag 08HY.
(blueprint: lem-sc-rectangle-qcoh-ordinary-compatibility)

Proof: Apply the faithful QCoh inclusion to the desired equality. Substitute the
component formulas for p.inv and b.hom, and the given formula for s.hom. The
upper-precomposition pasting law schemeDerivedBaseChange_pasting, transported
along hk₁ and hk₂, identifies the outer base-change map followed by the unit for
k and d.inv with the ordinary map for the pulled-back rectangle. To check this
transport, eliminate the two equalities, commute d.inv past the inverse upper
pullback comparison by naturality, and cancel d.hom/d.inv and the pullback
comparison/inverse. The horizontal law schemeDerivedBaseChange_horizontal_pasting
then identifies the successive inner and outer base-change maps with this
rectangle map conjugated by c(h,g) and c(t,p). The latter comparison cancels the
inverse present in s, giving the displayed equality. Reflect this equality through
the faithful inclusion. No ordinary base-change invertibility is used: the result
is the ordinary pasting step prior to inversion. The argument applies to zero
objects, empty schemes, and identity arrows without extra assumptions. -/
theorem rectangle_qcoh_ordinary_compatibility
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    let P := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
      (pullback.snd f (h ≫ g))
    let Q := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
      (pullback.snd (pullback.snd f g) h)
    let B := qcPullback (h ≫ g)
    let H := qcPullback g ⋙ qcPullback h
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let a := fun {A B : Scheme.{u}} (r : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction r
        (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) r))
    let d := conjugateIsoEquiv (a (pullback.snd (pullback.snd f g) h))
      ((a (pullback.snd f (h ≫ g))).comp (a k))
      (c k (pullback.snd f (h ≫ g)) ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hk₂))
    ∀ (s : U ⋙ L ≅ V) (_ : L.IsEquivalence) (_ : ∀ E : schemeDerivedQCohCategory X,
      (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map (s.hom.app E) =
        (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))
         (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
           eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
           (comp (pullback.fst (pullback.snd f g) h)
             (pullback.fst f g)).inv.app E.obj)),
    ∀ (p : L ⋙ Q ≅ P) (b : B ≅ H),
      (∀ D : schemeDerivedQCohCategory (pullback f (h ≫ g)),
        (schemeDerivedQCohProperty T).ι.map (p.inv.app D) =
          (schemeDerivedDirectImage (pullback.snd f (h ≫ g))).map
            ((a k).unit.app D.obj) ≫ d.inv.app ((derivedPullback k).obj D.obj)) →
      (∀ D : schemeDerivedQCohCategory Y,
        (schemeDerivedQCohProperty T).ι.map (b.hom.app D) = (c h g).inv.app D.obj) →
      ∀ E : schemeDerivedQCohCategory X,
        (qcBaseChange f (h ≫ g)).app E ≫ p.inv.app (U.obj E) ≫ Q.map (s.hom.app E) =
          b.hom.app ((qcDirectImage f).obj E) ≫
            (qcPullback h).map ((qcBaseChange f g).app E) ≫
            (@qcBaseChange _ (pullback f g) S T _
              (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
              (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
 := by
  classical
  intro U L V P Q B H c a d s hL hs p b hp hb E
  apply (schemeDerivedQCohProperty T).ι.map_injective
  simp only [Functor.map_comp]
  rw [hp, hb]
  have hsm := hs E
  change (s.hom.app E).hom = _ at hsm
  change schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
      (pullback.fst f (h ≫ g)) pullback.condition E.obj ≫
      ((schemeDerivedDirectImage (pullback.snd f (h ≫ g))).map
        ((a k).unit.app ((derivedPullback (pullback.fst f (h ≫ g))).obj E.obj)) ≫
        d.inv.app ((derivedPullback k).obj
          ((derivedPullback (pullback.fst f (h ≫ g))).obj E.obj))) ≫
      (schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h)).map
        (s.hom.app E).hom = _
  rw [hsm]
  let t := pullback.fst (pullback.snd f g) h
  let r := pullback.snd (pullback.snd f g) h
  let x := pullback.fst f g
  have ho : (t ≫ x) ≫ f = r ≫ (h ≫ g) := by
    dsimp only [t, r, x]
    rw [Category.assoc, pullback.condition,
      ← Category.assoc, pullback.condition, Category.assoc]
  have upper := upper_pasting_transport f (h ≫ g)
    (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g)) pullback.condition k
    (t ≫ x) r hk₁ hk₂ ho c a
    (schemeDerivedBaseChange_pasting f (h ≫ g)
      (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g)) pullback.condition k) E.obj
  change schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
      (pullback.fst f (h ≫ g)) pullback.condition E.obj ≫
      (schemeDerivedDirectImage (pullback.snd f (h ≫ g))).map
        ((a k).unit.app ((derivedPullback (pullback.fst f (h ≫ g))).obj E.obj)) ≫
      d.inv.app ((derivedPullback k).obj
        ((derivedPullback (pullback.fst f (h ≫ g))).obj E.obj)) ≫
      (schemeDerivedDirectImage r).map
        ((c k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
          eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁)) =
    schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ x) ho E.obj at upper
  have upper' := congrArg (fun z ↦ z ≫ (schemeDerivedDirectImage r).map
    ((c t x).inv.app E.obj)) upper
  change _ = (c h g).inv.app ((schemeDerivedDirectImage f).obj E.obj) ≫
    (derivedPullback h).map (schemeDerivedBaseChangeMap f (pullback.snd f g) g x
      pullback.condition E.obj) ≫
    schemeDerivedBaseChangeMap (pullback.snd f g) r h t pullback.condition
      ((derivedPullback x).obj E.obj)
  have horizontal :
      (derivedPullback h).map (schemeDerivedBaseChangeMap f (pullback.snd f g) g x
          pullback.condition E.obj) ≫
        schemeDerivedBaseChangeMap (pullback.snd f g) r h t pullback.condition
          ((derivedPullback x).obj E.obj) =
      (c h g).hom.app ((schemeDerivedDirectImage f).obj E.obj) ≫
        schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ x) ho E.obj ≫
        (schemeDerivedDirectImage r).map ((c t x).inv.app E.obj) := by
    exact schemeDerivedBaseChange_horizontal_pasting f g h x (pullback.snd f g) t r
      pullback.condition pullback.condition E.obj
  have horizontal' := congrArg (fun z ↦
    (c h g).inv.app ((schemeDerivedDirectImage f).obj E.obj) ≫ z) horizontal
  simp only [Iso.inv_hom_id_app_assoc] at horizontal'
  calc
    _ = schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ x) ho E.obj ≫
        (schemeDerivedDirectImage r).map ((c t x).inv.app E.obj) := by
      simpa only [Functor.map_comp, Category.assoc] using upper'
    _ = _ := horizontal'.symm

end AlgebraicGeometry
