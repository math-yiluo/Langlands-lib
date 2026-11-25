/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # First projection pasting for a shrinking graph intersection

Source: Stacks Project, Tags 0F7D and 0F7J, horizontal pasting and the
intersection calculation (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem triangle_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W T : Scheme.{u}} (t : X ⟶ V) (d : V ⟶ W) (e : W ⟶ T)
    (s : X ⟶ W) (q : X ⟶ T)
    [IsOpenImmersion d] [IsOpenImmersion e] [IsProper s] [IsProper q]
    (hd : t ≫ d = s) (he : s ≫ e = q) (M : DerivedCategoryModule A X) :
    D((e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t d s hd).hom.app M) ≫
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s e q he).hom.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) d e).inv.app (R((t)_*[ModuleCat.{u + 1} A]).obj M) ≫
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t (d ≫ e) q
          (by rw [← Category.assoc, hd, he])).hom.app M := by
  let sq : IsPullback s (𝟙 X) e q :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using he⟩
  have h := concrete_triangle_transport A t d e s (𝟙 X) q hd sq M
  have hh := congrArg (fun f ↦ f ≫ R((q)_*[ModuleCat.{u + 1} A]).map
    ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X).hom.app M)) h
  simpa only [rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj,
    Category.comp_id, Category.id_comp, Category.assoc] using hh

private theorem open_comp_assoc
    (A : Type (u + 1)) [CommRing A]
    {V W T S : Scheme.{u}} (d : V ⟶ W) (e : W ⟶ T) (b : T ⟶ S)
    [IsOpenImmersion d] [IsOpenImmersion e] [IsOpenImmersion b]
    (M : DerivedCategoryModule A V) :
    D((b)_!open[ModuleCat.{u + 1} A]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) d e).inv.app M) ≫
        (mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) (d ≫ e) b).inv.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) e b).inv.app
          (D((d)_!open[ModuleCat.{u + 1} A]).obj M) ≫
        (mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) d (e ≫ b)).inv.app M ≫
        (mapDerivedCategoryOpenImmersionLowerShriekCongr
          (ModuleCat.{u + 1} A) (Category.assoc d e b).symm).hom.app M := by
  have h := (unboundedFormalism A).shComp'_assoc_inv_app d e b
    (d ≫ e) (e ≫ b) ((d ≫ e) ≫ b) rfl rfl rfl (Category.assoc d e b).symm M
  simp_rw [unbounded_sh_comp] at h
  simpa only [mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_trans, Iso.trans_inv, NatTrans.comp_app, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app,
    Category.comp_id, unboundedFormalism] using h

private theorem inverse_triangle_extended
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W T S : Scheme.{u}} (t' : X ⟶ V) (d : V ⟶ W)
    (t : X ⟶ W) (e : W ⟶ T) (q : X ⟶ T) (b : T ⟶ S)
    (e' : V ⟶ T) [IsOpenImmersion d] [IsOpenImmersion e]
    [IsOpenImmersion e'] [IsOpenImmersion b] [IsProper t] [IsProper q]
    (hd : t' ≫ d = t) (he : t ≫ e = q) (he' : t' ≫ e' = q)
    (hde : d ≫ e = e') (M : DerivedCategoryModule A X) :
    D((b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t e q he).inv.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) e b).inv.app (R((t)_*[ModuleCat.{u + 1} A]).obj M) ≫
      D((e ≫ b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' d t hd).inv.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) d (e ≫ b)).inv.app
          (R((t')_*[ModuleCat.{u + 1} A]).obj M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) (by rw [← Category.assoc, hde])).hom.app
          (R((t')_*[ModuleCat.{u + 1} A]).obj M) =
    D((b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' e' q he').inv.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) e' b).inv.app
          (R((t')_*[ModuleCat.{u + 1} A]).obj M) := by
  subst e'
  have ht := triangle_comp A t' d e t q hd he M
  have hinv :
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t e q he).inv.app M ≫
        D((e)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' d t hd).inv.app M) =
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' (d ≫ e) q he').inv.app M ≫
        (mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) d e).hom.app
            (R((t')_*[ModuleCat.{u + 1} A]).obj M) := by
    apply (cancel_mono ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} A) d e).inv.app
        (R((t')_*[ModuleCat.{u + 1} A]).obj M))).1
    apply (cancel_mono
      ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' (d ≫ e) q he').hom.app
        M)).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  have hn := (mapDerivedCategoryOpenImmersionLowerShriekComp
    (ModuleCat.{u + 1} A) e b).inv.naturality
      ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' d t hd).inv.app M)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn.symm, ← Functor.map_comp_assoc, hinv, Functor.map_comp]
  have ha := open_comp_assoc A d e b (R((t')_*[ModuleCat.{u + 1} A]).obj M)
  simp only [Category.assoc]
  rw [← ha]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

private def first_side
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z P : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (p : P ⟶ Z) [IsProper p]
    (q : X ⟶ pullback (pullback.snd p c.g) c.i)
    (w : q ≫ pullback.snd (pullback.snd p c.g) c.i = 𝟙 X) :
    D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((c.g)_*[ModuleCat.{u + 1} A]) ≅
      R((q)_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.snd p c.g) c.i)_!open[ModuleCat.{u + 1} A]) ⋙
          R((pullback.fst p c.g ≫ p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((rightDerivedLowerStarIdIso A X).symm ≪≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        q (pullback.snd (pullback.snd p c.g) c.i) (𝟙 X) w).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
        (IsPullback.of_hasPullback (pullback.snd p c.g) c.i).flip) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (pullback.snd p c.g) c.g (pullback.fst p c.g ≫ p) pullback.condition.symm))

private theorem first_leg_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W T B Y : Scheme.{u}} (t' : X ⟶ V) (d : V ⟶ W)
    (t : X ⟶ W) (e : W ⟶ T) (q q' : X ⟶ T)
    (b : T ⟶ B) (p : B ⟶ Y) (e' : V ⟶ T)
    [IsOpenImmersion d] [IsOpenImmersion e] [IsOpenImmersion e']
    [IsOpenImmersion b] [IsProper t] [IsProper q] [IsProper q']
    (hd : t' ≫ d = t) (he : t ≫ e = q) (he' : t' ≫ e' = q')
    (hde : d ≫ e = e') (hq : q' = q)
    (F : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y)
    (P : (X ⟶ T) → Prop)
    (side : ∀ q, P q → (F ≅ R((q)_*[ModuleCat.{u + 1} A]) ⋙
      D((b)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A])))
    (w : P q) (w' : P q') :
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
            (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t e q he).symm _ ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _
            (mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) e b).symm) R((p)_*[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _).hom ≫
      (Functor.isoWhiskerRight
          (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' d t hd).symm
          (D((e ≫ b)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            ((mapDerivedCategoryOpenImmersionLowerShriekComp
                (ModuleCat.{u + 1} A) d (e ≫ b)).symm ≪≫
              mapDerivedCategoryOpenImmersionLowerShriekCongr
                (ModuleCat.{u + 1} A) (by rw [← Category.assoc, hde]))
            R((p)_*[ModuleCat.{u + 1} A]))).hom =
      ((side q w).symm ≪≫ side q' w').hom ≫
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (Functor.isoWhiskerRight
                (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t' e' q'
                  he').symm _ ≪≫
              Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft _
                (mapDerivedCategoryOpenImmersionLowerShriekComp
                  (ModuleCat.{u + 1} A) e' b).symm) R((p)_*[ModuleCat.{u + 1} A]) ≪≫
          Functor.associator _ _ _).hom := by
  subst hq
  simp only [Iso.symm_self_id, Iso.refl_hom, Category.id_comp]
  apply NatTrans.ext
  funext M
  have hraw := inverse_triangle_extended A t' d t e q' b e' hd he he' hde M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj,
    Category.id_comp, Category.comp_id, Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun f ↦ R((p)_*[ModuleCat.{u + 1} A]).map f) hraw

/-- The inverse first triangle commutes with passing to the smaller intersection.
Source: Stacks Project, more-etale.tex, lemma-shriek-proper-and-open-compose-horizontal
(Tag 0F7D), specialized to the first intersection projection in the product-graph
extension of the independence calculation of lemma-shriek-composition (Tag 0F7J).
(auxiliary; not a blueprint node).

Proof: write I and I' for the intersections, d:I'→I for graphIntersectionShrink,
s and s' for their proper graph lifts, and u:I→O1 and u':I'→O1 for the first
projections. Both u and u' are open, d u = u', and s' d = s. The first graph
lift is unchanged by graphFirstLift_shrink. All the identity-top squares for
these lifts and inclusions are Cartesian, since the inclusions are monomorphisms.
Apply the horizontal pasting clause of etaleProperOpenExchangeCube to the
identity-top squares for d and u. Its Cartesian normalization identifies their
exchanges with the exchanges in the definition of the proper/open triangles.
Remove extension by the identity with mapDerivedCategoryOpenImmersionLowerShriekId.
The two resulting triangles compose to the triangle for u'. Invert this equation,
whisker by extension along b1:O1→T, and compose the open extensions. Associativity
of openImmersionLowerShriekComp, descended to derived categories, identifies the
compositors for d,u,b1. Now whisker by the common ambient proper image and insert
the displayed functor associators. This compares exactly graphIntersectionLeg₁
followed by graphIntersectionShrinkIso with the smaller first leg, under the
canonical identification of the unchanged first graph word. The first side formula
locallyClosedGraphSide₁ depends only on this unchanged graph lift and the fixed
ambient projections; consequently that identification is graphFirstShrinkIso.
No second projection, second-neighborhood triangle, or middle comparison is used.
Identity and empty opens obey the same equations. -/
theorem etaleGraphShrinkFirstLeg
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    (H.graphIntersectionLeg₁ c A).hom ≫ (H.graphIntersectionShrinkIso c A a' v fac).hom =
      (H.graphFirstShrinkIso c A a' v fac).hom ≫
        ((H.shrink a' v fac).graphIntersectionLeg₁ c A).hom := by
  let S := H.shrink a' v fac
  let d := H.graphIntersectionShrink c a' v fac
  let e := pullback.fst
    (pullback.fst (pullback.snd H.p c.g) c.i)
    (pullback.fst (pullback.fst H.p c.g) H.e)
  let e' := pullback.fst
    (pullback.fst (pullback.snd H.p c.g) c.i)
    (pullback.fst (pullback.fst H.p c.g) (v ≫ H.e))
  let b := pullback.fst (pullback.snd H.p c.g) c.i
  have he : H.graphS₁₂ c ≫ e = H.graphS₁ c := pullback.lift_fst _ _ _
  have he' : S.graphS₁₂ c ≫ e' = S.graphS₁ c := pullback.lift_fst _ _ _
  have hd : S.graphS₁₂ c ≫ d = H.graphS₁₂ c :=
    H.graphIntersectionShrink_graph c a' v fac
  have hde : d ≫ e = e' := H.graphIntersectionShrink_fst c a' v fac
  exact first_leg_pasting A (S.graphS₁₂ c) d (H.graphS₁₂ c) e
    (H.graphS₁ c) (S.graphS₁ c) b (pullback.fst H.p c.g ≫ H.p) e'
    hd he he' hde (H.graphFirstLift_shrink c a' v fac)
    (D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((c.g)_*[ModuleCat.{u + 1} A]))
    (fun q ↦ q ≫ pullback.snd (pullback.snd H.p c.g) c.i = 𝟙 X)
    (fun q w ↦ first_side A c H.p q w)
    (by simp only [EtaleGraphPresentation.graphS₁, locallyClosedGraphS₁,
      pullback.lift_snd])
    (by simp only [S, EtaleGraphPresentation.graphS₁, locallyClosedGraphS₁,
      EtaleGraphPresentation.shrink, pullback.lift_snd])

end AlgebraicGeometry.Etale
