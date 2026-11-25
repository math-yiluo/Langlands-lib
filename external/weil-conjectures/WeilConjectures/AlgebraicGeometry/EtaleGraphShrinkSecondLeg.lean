/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Second projection pasting for a shrinking graph intersection

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
  locallyClosedGraphS₁₂ locallyClosedGraphS₂
  EtaleGraphPresentation.graphIntersectionShrink EtaleGraphPresentation.graphNeighborhoodShrink

private theorem triangle_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I J K : Scheme.{u}} (t : X ⟶ I) (a : I ⟶ J) (b : J ⟶ K)
    (s : X ⟶ J) (z : X ⟶ K)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsProper s] [IsProper z]
    (ht : t ≫ a = s) (hz : s ≫ b = z) (M : DerivedCategoryModule A X) :
    D((b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t a s ht).hom.app M) ≫
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s b z hz).hom.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) a b).inv.app (R((t)_*[ModuleCat.{u + 1} A]).obj M) ≫
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t (a ≫ b) z
          (by rw [← Category.assoc, ht, hz])).hom.app M := by
  let sq : IsPullback s (𝟙 X) b z :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hz⟩
  have hh := congrArg
    (fun q ↦ q ≫ R((z)_*[ModuleCat.{u + 1} A]).map
      ((mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} A) X).hom.app M))
    (concrete_triangle_transport A t a b s (𝟙 X) z ht sq M)
  simpa only [rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.id_obj, Category.comp_id, Category.assoc] using hh

private def openComp
    (A : Type (u + 1)) [CommRing A] {I J K : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ K) (c : I ⟶ K)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] (hc : a ≫ b = c) :=
  mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hc.symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b

private theorem openComp_assoc
    (A : Type (u + 1)) [CommRing A] {I J K T : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ K) (e : K ⟶ T)
    (ab : I ⟶ K) (be : J ⟶ T) (w : I ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion e]
    [IsOpenImmersion ab] [IsOpenImmersion be] [IsOpenImmersion w]
    (hab : a ≫ b = ab) (hbe : b ≫ e = be) (hw : ab ≫ e = w) (hw' : a ≫ be = w)
    (M : DerivedCategoryModule A I) :
    (openComp A ab e w hw).hom.app M ≫
        D((e)_!open[ModuleCat.{u + 1} A]).map ((openComp A a b ab hab).hom.app M) =
      (openComp A a be w hw').hom.app M ≫
        (openComp A b e be hbe).hom.app (D((a)_!open[ModuleCat.{u + 1} A]).obj M) := by
  have hh := congr_app
    ((unboundedFormalism A).shComp'_assoc a b e ab be w hab hbe hw hw') M
  rw [unbounded_sh_comp, unbounded_sh_comp, unbounded_sh_comp,
    unbounded_sh_comp] at hh
  simpa only [openComp, unboundedFormalism, Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.comp_id] using hh

private def extendedTriangle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I J T : Scheme.{u}} (t : X ⟶ I) (a : I ⟶ J) (s : X ⟶ J)
    (b : J ⟶ T) (w : I ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion w] [IsProper s]
    (ht : t ≫ a = s) (hw : a ≫ b = w) :
    R((t)_*[ModuleCat.{u + 1} A]) ⋙ D((w)_!open[ModuleCat.{u + 1} A]) ≅
      R((s)_*[ModuleCat.{u + 1} A]) ⋙ D((b)_!open[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerLeft _ (openComp A a b w hw) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t a s ht) _

private theorem extendedTriangle_trans
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I J K T : Scheme.{u}} (t : X ⟶ I) (a : I ⟶ J) (s : X ⟶ J)
    (b : J ⟶ K) (z : X ⟶ K) (e : K ⟶ T) (be : J ⟶ T) (w : I ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion e]
    [IsOpenImmersion be] [IsOpenImmersion w] [IsProper s] [IsProper z]
    (ht : t ≫ a = s) (hz : s ≫ b = z) (hbe : b ≫ e = be) (hw : a ≫ be = w) :
    (extendedTriangle A t a s be w ht hw).hom ≫
        (extendedTriangle A s b z e be hz hbe).hom =
      (extendedTriangle A t (a ≫ b) z e w
        (by rw [← Category.assoc, ht, hz])
        (by rw [Category.assoc, hbe, hw])).hom := by
  ext M
  simp only [extendedTriangle, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc]
  rw [(openComp A b e be hbe).hom.naturality_assoc]
  simp only [Functor.comp_obj]
  rw [← Category.assoc,
    ← openComp_assoc A a b e (a ≫ b) be w rfl hbe
      (by rw [Category.assoc, hbe, hw]) hw]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [triangle_comp]
  simp only [openComp, mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_trans, Iso.hom_inv_id_app_assoc]

private theorem extendedTriangle_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I J T : Scheme.{u}} (t : X ⟶ I) (s : X ⟶ J) (b : J ⟶ T) (w : I ⟶ T)
    {a a' : I ⟶ J} [IsOpenImmersion a] [IsOpenImmersion a']
    [IsOpenImmersion b] [IsOpenImmersion w] [IsProper s]
    (h : a = a') (ht : t ≫ a = s) (ht' : t ≫ a' = s)
    (hw : a ≫ b = w) (hw' : a' ≫ b = w) :
    (extendedTriangle A t a s b w ht hw).hom =
      (extendedTriangle A t a' s b w ht' hw').hom := by
  subst a'
  rfl

private theorem openCongr_symm_inv
    (A : Type (u + 1)) [CommRing A] {I T : Scheme.{u}}
    {a b : I ⟶ T} [IsOpenImmersion a] [IsOpenImmersion b] (h : a = b) :
    (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) h.symm).inv =
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) h).hom := by
  subst b
  rfl

private theorem openComp_hom
    (A : Type (u + 1)) [CommRing A] {I J T : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ T) (w : I ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion w] (h : a ≫ b = w) :
    (openComp A a b w h).hom =
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) h.symm).hom ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b).hom := by
  rfl

private theorem openComp_inv
    (A : Type (u + 1)) [CommRing A] {I J T : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ T) (w : I ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion w] (h : a ≫ b = w) :
    (openComp A a b w h).inv =
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b).inv ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).hom := by
  change (mapDerivedCategoryOpenImmersionLowerShriekComp
    (ModuleCat.{u + 1} A) a b).inv ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) h.symm).inv = _
  rw [openCongr_symm_inv]

attribute [local irreducible] openComp

/-- The second triangle commutes with the intersection and neighborhood shrinkings.
Source: Stacks Project, more-etale.tex, lemma-shriek-proper-and-open-compose-horizontal
(Tag 0F7D), specialized to the second intersection projection in the product-graph
extension of the independence calculation of lemma-shriek-composition (Tag 0F7J).
(auxiliary; not a blueprint node).

Proof: let d:I'→I be graphIntersectionShrink, v2:O2'→O2 be
graphNeighborhoodShrink, and u2:I→O2, u2':I'→O2' be the second projections.
The constructed map satisfies d u2 = u2' v2. Its proper graph lifts satisfy
s' d = s, s u2 = s2, s' u2' = s2' and s2' v2 = s2. All four inclusions are
open. Apply horizontal pasting of the normalized proper/open exchange to the
two strings of identity-top Cartesian squares (d,u2) and (u2',v2).
The common composite inclusion is the same by d u2 = u2' v2, so the two
composite triangles agree after the canonical equality transport. Remove the
identity open extensions with their unitors and solve the equality for the
inverse neighborhood triangle. Whisker with extension along b2:O2→T.
Use associativity of open extension composition to combine v2,b2 and d,u2,b2.
The pullback equations u1 b1 = u2 b2 and u1' b1 = u2' b2' identify these
open words with the first-projection convention in graphIntersectionWord;
b2' = v2 b2 is graphNeighborhoodShrink_open_fac. Naturality of the open
compositors moves these equality comparisons through the two triangles.
Whisker by the common ambient proper image and insert the associators.
The resulting two paths are exactly graphIntersectionLeg₂ followed by
graphNeighborhoodTriangle and graphIntersectionShrinkIso followed by the
smaller second leg. This uses no first triangle and no full middle comparison.
Identity and empty opens obey the same equations. -/
theorem etaleGraphShrinkSecondLeg
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    (H.graphIntersectionLeg₂ c A).hom ≫ (H.graphNeighborhoodTriangle c A a' v fac).hom =
      (H.graphIntersectionShrinkIso c A a' v fac).hom ≫
        ((H.shrink a' v fac).graphIntersectionLeg₂ c A).hom := by
  let S := H.shrink a' v fac
  let t := S.graphS₁₂ c
  let s := H.graphS₁₂ c
  let z := H.graphS₂ c
  let z' := S.graphS₂ c
  let d := H.graphIntersectionShrink c a' v fac
  let n := H.graphNeighborhoodShrink c a' v fac
  let u := pullback.snd (pullback.fst (pullback.snd H.p c.g) c.i)
    (pullback.fst (pullback.fst H.p c.g) H.e)
  let u' := pullback.snd (pullback.fst (pullback.snd H.p c.g) c.i)
    (pullback.fst (pullback.fst H.p c.g) (v ≫ H.e))
  let b := pullback.fst (pullback.fst H.p c.g) H.e
  let b' := pullback.fst (pullback.fst H.p c.g) (v ≫ H.e)
  let w := H.graphIntersectionOpen c
  let w' := S.graphIntersectionOpen c
  have hs : s ≫ u = z := by
    dsimp only [s, u, z, EtaleGraphPresentation.graphS₁₂, EtaleGraphPresentation.graphS₂]
    simp only [locallyClosedGraphS₁₂, pullback.lift_snd]
  have ht : t ≫ u' = z' := by
    dsimp only [t, u', z', S, EtaleGraphPresentation.graphS₁₂,
      EtaleGraphPresentation.graphS₂, EtaleGraphPresentation.shrink]
    simp only [locallyClosedGraphS₁₂, pullback.lift_snd]
  have hw : u ≫ b = w := pullback.condition.symm
  have hw' : u' ≫ b' = w' := pullback.condition.symm
  have hd : t ≫ d = s := H.graphIntersectionShrink_graph c a' v fac
  have hn : z' ≫ n = z := H.graphNeighborhoodShrink_graph c a' v fac
  have hdw : d ≫ w = w' := H.graphIntersectionShrink_open_fac c a' v fac
  have hnb : n ≫ b = b' := H.graphNeighborhoodShrink_open_fac c a' v fac
  let E := extendedTriangle A s u z b w hs hw
  let E' := extendedTriangle A t u' z' b' w' ht hw'
  let D := extendedTriangle A t d s w w' hd hdw
  let N := extendedTriangle A z' n z b b' hn hnb
  have h₁ := extendedTriangle_trans A t d s u z b w w' hd hs hw hdw
  have h₂ := extendedTriangle_trans A t u' z' n z b b' w' ht hn hnb hw'
  have hdu : d ≫ u = u' ≫ n := H.graphIntersectionShrink_snd c a' v fac
  have hc := extendedTriangle_congr A t z b w' hdu
    (by rw [← Category.assoc, hd, hs]) (by rw [← Category.assoc, ht, hn])
    (by rw [Category.assoc, hw, hdw]) (by rw [Category.assoc, hnb, hw'])
  have hraw : E.hom ≫ N.inv = D.inv ≫ E'.hom := by
    apply (cancel_epi D.hom).1
    apply (cancel_mono N.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc,
      Category.comp_id] using h₁.trans (hc.trans h₂.symm)
  ext M
  have hh := congrArg
    (fun q ↦ R((pullback.fst H.p c.g ≫ H.p)_*[ModuleCat.{u + 1} A]).map q)
    (congr_app hraw M)
  simp only [E, E', D, N, extendedTriangle, openComp_hom, openComp_inv,
    EtaleGraphPresentation.graphIntersectionLeg₂,
    EtaleGraphPresentation.graphNeighborhoodTriangle,
    EtaleGraphPresentation.graphIntersectionShrinkIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Category.assoc,
    Category.id_comp, Category.comp_id] at hh ⊢
  exact hh

end AlgebraicGeometry.Etale
