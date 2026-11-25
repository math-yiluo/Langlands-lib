/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting

/-! # Shrinking the supporting open in the explicit graph comparison

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, and the
product/intersection formula of `EtaleLocallyClosedGraphModel`.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem side_square_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X O O' U W T P : Scheme.{u}}
    (s : X ⟶ O) (s' : X ⟶ O') (a : X ⟶ U) (a' : X ⟶ W)
    (q : O ⟶ U) (q' : O' ⟶ W) (p : T ⟶ P)
    (b : O ⟶ T) (b' : O' ⟶ T) (e : U ⟶ P) (v : W ⟶ U) (ρ : O' ⟶ O)
    [IsProper s] [IsProper s'] [IsProper a] [IsProper a']
    [IsProper q] [IsProper q'] [IsProper p]
    [IsOpenImmersion b] [IsOpenImmersion b'] [IsOpenImmersion e]
    [IsOpenImmersion v] [IsOpenImmersion ρ]
    (sq : IsPullback q b e p) (sv : IsPullback q' ρ v q)
    (hs : s' ≫ ρ = s) (ha : s ≫ q = a) (ha' : s' ≫ q' = a')
    (hb : ρ ≫ b = b') (hv : a' ≫ v = a)
    (M : DerivedCategoryModule A X) :
    D((e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) s q a ha).inv.app M) ≫
      (openImmersionLowerShriekLowerStarExchangeIso A sq).hom.app
        (R((s)_*[ModuleCat.{u + 1} A]).obj M) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        (D((b)_!open[ModuleCat.{u + 1} A]).map
            ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s' ρ s hs).inv.app M) ≫
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) ρ b).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hb).hom.app
              (R((s')_*[ModuleCat.{u + 1} A]).obj M)) =
    D((e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v a hv).inv.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) v e).inv.app
          (R((a')_*[ModuleCat.{u + 1} A]).obj M) ≫
      D((v ≫ e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) s' q' a' ha').inv.app M) ≫
      (openImmersionLowerShriekLowerStarExchangeIso A
        (by simpa only [hb] using sv.paste_vert sq)).hom.app
          (R((s')_*[ModuleCat.{u + 1} A]).obj M) := by
  subst a
  subst a'
  subst b'
  obtain ⟨θ, Γ, hθ, hrep, hcart, hvert, hhor, hvi, hhi, hcube⟩ :=
    etaleProperOpenExchangeCube A
  -- E is the identity-top graph square; D_v lies below it.
  let se : IsPullback s' (𝟙 X) ρ s :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hs⟩
  have ve := hvert (𝟙 X) ρ v s' s q' q se.toCommSq.flip sv.toCommSq.flip M
  -- The smaller side square is D_v followed horizontally by D_H.
  have ho := hhor ρ b v e q' q p sv.toCommSq.flip sq.toCommSq.flip
    (R((s')_*[ModuleCat.{u + 1} A]).obj M)
  have ce := hcart (𝟙 X) s' s ρ se
  have cv := hcart ρ q' q v sv
  have ch := hcart b q p e sq
  have cs := hcart (ρ ≫ b) q' p (v ≫ e) (sv.paste_vert sq)
  have cq := hcart (𝟙 X) (s' ≫ q') (s ≫ q) v (se.paste_horiz sv)
  -- Remove the identity open from vertical pasting by compositor naturality.
  have vnorm :
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        (s' ≫ q') v (s ≫ q) hv).hom.app M =
      D((v)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s' q').inv.app M) ≫
        (Γ ρ q' q v sv.toCommSq.flip).hom.app
          (R((s')_*[ModuleCat.{u + 1} A]).obj M) ≫
        R((q)_*[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s' ρ s hs).hom.app M) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s q).hom.app M := by
    rw [cq, cv, ce] at ve
    simp only [rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      openImmersionLowerShriekLowerStarExchangeIso, asIso_hom, Functor.comp_obj,
      Functor.id_obj, Functor.id_map, Category.comp_id]
    rw [cv, ve]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s q).hom.naturality]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [cv, ch, cs] at ho
  rw [cv] at vnorm
  let C := rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s q
  let C' := rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s' q'
  let δ := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s' ρ s hs
  let η := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
    (s' ≫ q') v (s ≫ q) hv
  let E := D((e)_!open[ModuleCat.{u + 1} A])
  let V := D((v)_!open[ModuleCat.{u + 1} A])
  let B := D((b)_!open[ModuleCat.{u + 1} A])
  let Q := R((q)_*[ModuleCat.{u + 1} A])
  let P := R((p)_*[ModuleCat.{u + 1} A])
  let α := mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) v e
  let β := mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) ρ b
  let γ := openImmersionLowerShriekLowerStarExchangeIso A sq
  let γv := openImmersionLowerShriekLowerStarExchangeIso A sv
  let γs := openImmersionLowerShriekLowerStarExchangeIso A (sv.paste_vert sq)
  -- Solve vertical pasting for the inverse graph triangle.
  have vinv : C.inv.app M ≫ Q.map (δ.inv.app M) =
      η.inv.app M ≫ V.map (C'.inv.app M) ≫
        γv.hom.app (R((s')_*[ModuleCat.{u + 1} A]).obj M) := by
    have hh := congrArg (fun z ↦ η.inv.app M ≫ z ≫ C.inv.app M ≫
      Q.map (δ.inv.app M)) vnorm
    change η.inv.app M ≫ η.hom.app M ≫ C.inv.app M ≫ Q.map (δ.inv.app M) =
      η.inv.app M ≫ (V.map (C'.inv.app M) ≫ γv.hom.app _ ≫
        Q.map (δ.hom.app M) ≫ C.hom.app M) ≫ C.inv.app M ≫
          Q.map (δ.inv.app M) at hh
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.comp_obj, Functor.map_id, Category.comp_id] at hh
    rw [Q.map_id, Category.comp_id] at hh
    exact hh
  change γs.hom.app _ = α.hom.app _ ≫ E.map (γv.hom.app _) ≫
    γ.hom.app _ ≫ P.map (β.inv.app _) at ho
  simp only [rightDerivedLowerStarCompOfEq,
    mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.trans_refl,
    Iso.symm_hom]
  change E.map (C.inv.app M) ≫ γ.hom.app _ ≫
      P.map (B.map (δ.inv.app M) ≫ β.inv.app _) =
    E.map (η.inv.app M) ≫ α.inv.app _ ≫
      D((v ≫ e)_!open[ModuleCat.{u + 1} A]).map (C'.inv.app M) ≫ γs.hom.app _
  -- Substitute horizontal pasting and move the inverse triangle through D_H.
  rw [ho]
  rw [← reassoc_of% α.inv.naturality (C'.inv.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [← reassoc_of% γ.hom.naturality (δ.inv.app M)]
  change E.map (C.inv.app M) ≫ E.map (Q.map (δ.inv.app M)) ≫ _ =
    E.map (η.inv.app M) ≫ E.map (V.map (C'.inv.app M)) ≫ E.map (γv.hom.app _) ≫ _
  rw [← reassoc_of% E.map_comp, vinv]
  simp only [Functor.map_comp, Category.assoc]

private theorem shrink_cancel
    {C : Type*} [Category C] {B O₁ O₂ N₁ N₂ F₁ F₂ : C}
    (a₁ : B ≅ O₁) (a₂ : B ≅ O₂) (m₁ : O₁ ≅ N₁) (m₂ : O₂ ≅ N₂)
    (b₁ : F₁ ≅ N₁) (b₂ : F₂ ≅ N₂) (T : N₁ ≅ N₂) (I : F₁ ≅ F₂)
    (hs : b₁.hom ≫ T.hom = I.hom ≫ b₂.hom)
    (hm : m₁.hom ≫ T.hom = (a₁.symm ≪≫ a₂).hom ≫ m₂.hom) :
    (a₁ ≪≫ m₁ ≪≫ b₁.symm) ≪≫ I = a₂ ≪≫ m₂ ≪≫ b₂.symm := by
  apply Iso.ext
  apply (cancel_mono b₂.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← hs]
  simp only [Iso.inv_hom_id_assoc]
  rw [hm]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The explicit graph comparison commutes with shrinking the supporting open while
keeping its ambient proper scheme fixed.

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D; the elementary
neighborhood move in lem-pur-etale-graph-comparison-interchange, steps 1--3.
(auxiliary; not a blueprint node).

Proof: the two graph products with `c.Z` have the same ambient scheme and the same
first supporting neighborhood. The smaller second neighborhood is the inverse
image of `v`, and its intersection with the first neighborhood is the corresponding
open subspace of the old intersection. The graph lifts factor through both smaller
opens since `ha` holds. All graph lifts are proper by proper-to-separated, and all
the resulting identity-top graph squares are Cartesian since their bottom arrows
are monomorphisms. Expand the two graph comparisons as `B₂⁻¹ R(B₁₂) B₁`.
Let `D_v` be the Cartesian neighborhood square with top the smaller open inclusion
and bottom `v`, and let `E` be its identity-top graph triangle. The smaller side
square is `D_v` pasted horizontally before the old side square. The triangle for
`ha` is `E` stacked vertically above `D_v`. Apply the two pasting laws, cancel the
common exchange for `D_v`, and move the exchange for `E` past the old side exchange
by naturality. This compares the second side words. For the middle words apply
horizontal pasting to the intersection graph triangle followed by each projection;
the two occurrences of the smaller-intersection triangle cancel. Substitute the
side and middle equations into the graph words. The remaining factor is the inverse
triangle interchange followed by the canonical open compositor, with `he` identifying
the composite open. This is the word below.
The identity direct image on the first side is the same in both formulas and cancels.
The proof does not require quasi-compactness and is valid for identity or empty opens. -/
theorem etaleGraphComparisonFromOpen_openShrink
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s : EtaleGraphPresentation f) {W : Scheme.{u}}
    (a' : X ⟶ W) [IsProper a'] (v : W ⟶ s.U) [IsOpenImmersion v]
    (e' : W ⟶ s.P) [IsOpenImmersion e']
    (ha : a' ≫ v = s.a) (he : v ≫ s.e = e') :
    let t : EtaleGraphPresentation f := {
      U := W
      P := s.P
      a := a'
      e := e'
      p := s.p
      fac := by
        calc
          a' ≫ e' ≫ s.p = (a' ≫ v) ≫ s.e ≫ s.p := by
            rw [← he]
            simp only [Category.assoc]
          _ = f := by rw [ha]; exact s.fac }
    etaleGraphComparisonFromOpen A c s ≪≫
        Functor.isoWhiskerRight
          (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v s.a ha).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            ((mapDerivedCategoryOpenImmersionLowerShriekComp
                (ModuleCat.{u + 1} A) v s.e).symm ≪≫
              mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) he) _) =
      etaleGraphComparisonFromOpen A c t := by
  subst e'
  dsimp only
  have hside : (s.graphSide₂ c A).hom ≫
      (s.graphNeighborhoodTriangle c A a' v ha).hom =
      (etaleGraphShrinkInterchange A s a' v ha).hom ≫
        ((s.shrink a' v ha).graphSide₂ c A).hom := by
    apply NatTrans.ext
    funext M
    have hc := side_square_pasting A (s.graphS₂ c) ((s.shrink a' v ha).graphS₂ c)
      s.a a' (pullback.snd _ _) (pullback.snd _ _) (pullback.fst s.p c.g)
      (pullback.fst _ _) (pullback.fst _ _) s.e v
      (s.graphNeighborhoodShrink c a' v ha)
      (IsPullback.of_hasPullback (pullback.fst s.p c.g) s.e).flip
      (s.graphNeighborhoodShrink_isPullback c a' v ha).flip
      (s.graphNeighborhoodShrink_graph c a' v ha)
      (by simp only [EtaleGraphPresentation.graphS₂, locallyClosedGraphS₂,
        pullback.lift_snd])
      (by simp only [EtaleGraphPresentation.graphS₂, locallyClosedGraphS₂,
        pullback.lift_snd, EtaleGraphPresentation.shrink])
      (s.graphNeighborhoodShrink_open_fac c a' v ha) ha M
    let R := R((s.p)_*[ModuleCat.{u + 1} A])
    let C := rightDerivedLowerStarComp (ModuleCat.{u + 1} A)
      (pullback.fst s.p c.g) s.p
    have hh := congrArg (fun z ↦ R.map z ≫ C.hom.app
      (D((pullback.fst (pullback.fst s.p c.g) (v ≫ s.e))_!open[
        ModuleCat.{u + 1} A]).obj
        (R(((s.shrink a' v ha).graphS₂ c)_*[ModuleCat.{u + 1} A]).obj M))) hc
    simp only [EtaleGraphPresentation.graphSide₂, locallyClosedGraphSide₂,
      EtaleGraphPresentation.graphNeighborhoodTriangle, etaleGraphShrinkInterchange,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Functor.comp_map, Category.comp_id, Category.id_comp,
      rightDerivedLowerStarCompOfEq, Iso.refl_hom, Functor.map_id, Category.assoc]
    rw [← reassoc_of% C.hom.naturality, ← C.hom.naturality]
    simpa only [R, C, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.comp_map, Category.assoc,
      EtaleGraphPresentation.shrink, EtaleGraphPresentation.graphS₂,
      rightDerivedLowerStarCompOfEq] using hh
  have hmiddle := etaleGraphShrinkMiddlePasting A c s a' v ha
  have hfrom (t : EtaleGraphPresentation f) :
      etaleGraphComparisonFromOpen A c t =
        t.graphSide₁ c A ≪≫ t.graphMiddle c A ≪≫ (t.graphSide₂ c A).symm := by
    apply Iso.ext
    simp only [etaleGraphComparisonFromOpen, locallyClosedGraphIso,
      EtaleGraphPresentation.graphSide₁, EtaleGraphPresentation.graphSide₂,
      EtaleGraphPresentation.graphMiddle, Iso.trans_hom, Category.assoc]
  have h := shrink_cancel (s.graphSide₁ c A) ((s.shrink a' v ha).graphSide₁ c A)
    (s.graphMiddle c A) ((s.shrink a' v ha).graphMiddle c A)
    (s.graphSide₂ c A) ((s.shrink a' v ha).graphSide₂ c A)
    (s.graphNeighborhoodTriangle c A a' v ha) (etaleGraphShrinkInterchange A s a' v ha)
    hside hmiddle
  rw [← hfrom s, ← hfrom (s.shrink a' v ha)] at h
  simpa only [etaleGraphShrinkInterchange,
    mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.trans_refl,
    EtaleGraphPresentation.shrink] using h

end AlgebraicGeometry.Etale
