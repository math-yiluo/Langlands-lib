import Langlands.GroupScheme.Reductive.AffinePinnedAtlasTransitions

/-! # Actual descent datum from corrected pinned atlas transitions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedAtlas

open Descent

variable {S T W : Scheme.{u}} {G : GroupScheme S}
    (A : AffinePinnedAtlas G)

/-- The original group pulled back to the actual atlas scheme. -/
abbrev group : GroupScheme A.space := (baseChange A.projection).obj G

/-- Express the corrected direct-pullback transition between actual atlas pullbacks. -/
def actualTransition (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    (baseChange a).obj A.group ≅ (baseChange b).obj A.group :=
  pullbackComparison A.projection a k ha G ≪≫ A.transition P a b k ha hb ≪≫
    (pullbackComparison A.projection b k hb G).symm

/-- Actual atlas transitions commute with arbitrary further pullback. -/
theorem actualTransition_pull (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (q : W ⟶ T) (r s : W ⟶ A.space)
    (hr : q ≫ a = r) (hs : q ≫ b = s) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hr hs (A.actualTransition P a b k ha hb) =
      A.actualTransition P r s l
        (by rw [← hr, Category.assoc, ha, hl])
        (by rw [← hs, Category.assoc, hb, hl]) := by
  subst r
  subst s
  let cf := pullbackComparison A.projection a k ha G
  let cg := pullbackComparison A.projection b k hb G
  let cr := pullbackComparison A.projection (q ≫ a) l
    (by rw [Category.assoc, ha, hl]) G
  let cs := pullbackComparison A.projection (q ≫ b) l
    (by rw [Category.assoc, hb, hl]) G
  let af := pullbackComparison a q (q ≫ a) rfl A.group
  let ag := pullbackComparison b q (q ≫ b) rfl A.group
  let bk := pullbackComparison k q l hl G
  have hca := congrArg Iso.hom
    (pullbackComparison_comp A.projection a k ha q l hl G)
  have hcb := congrArg Iso.hom
    (pullbackComparison_comp A.projection b k hb q l hl G)
  change (baseChange q).map cf.hom ≫ bk.hom = af.hom ≫ cr.hom at hca
  change (baseChange q).map cg.hom ≫ bk.hom = ag.hom ≫ cs.hom at hcb
  have hsrc : af.inv ≫ (baseChange q).map cf.hom = cr.hom ≫ bk.inv := by
    apply (cancel_mono bk.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hca]
    exact Iso.inv_hom_id_assoc af cr.hom
  have htgt : (baseChange q).map cg.inv ≫ ag.hom = bk.hom ≫ cs.inv := by
    apply (cancel_epi ((baseChange q).map cg.hom)).mp
    rw [← Category.assoc, Iso.map_hom_inv_id, Category.id_comp,
      ← Category.assoc, hcb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold actualTransition
  rw [← A.transition_pull P a b k ha hb q l hl]
  apply Iso.ext
  change af.inv ≫
      (baseChange q).map (cf.hom ≫ (A.transition P a b k ha hb).hom ≫ cg.inv) ≫
      ag.hom =
    cr.hom ≫ (bk.inv ≫ (baseChange q).map (A.transition P a b k ha hb).hom ≫
      bk.hom) ≫ cs.inv
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc af.inv ((baseChange q).map cf.hom), hsrc, htgt]
  simp only [Category.assoc]

/-- Actual transitions compose on every common test scheme. -/
theorem actualTransition_trans (P : RelativePinnedComparison.{u})
    (a b c : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k)
    (hc : c ≫ A.projection = k) :
    A.actualTransition P a c k ha hc =
      A.actualTransition P a b k ha hb ≪≫ A.actualTransition P b c k hb hc := by
  apply Iso.ext
  simp [actualTransition, A.transition_trans P a b c k ha hb hc]

/-- The actual corrected isomorphism on the atlas double overlap. -/
def overlap (P : RelativePinnedComparison.{u}) : OverlapIso A.projection A.group :=
  A.actualTransition P (fst A.projection) (snd A.projection)
    (fst A.projection ≫ A.projection) rfl pullback.condition.symm

/-- Every pullback of the overlap has the prescribed actual transition. -/
theorem overlap_pull (P : RelativePinnedComparison.{u})
    (q : T ⟶ Overlap A.projection) (a b : T ⟶ A.space)
    (ha : q ≫ fst A.projection = a) (hb : q ≫ snd A.projection = b)
    (k : T ⟶ S) (hk : a ≫ A.projection = k) :
    pullIso q ha hb (A.overlap P) =
      A.actualTransition P a b k hk
        (by rw [← hb, Category.assoc, ← pullback.condition, ← Category.assoc, ha, hk]) := by
  exact A.actualTransition_pull P _ _ _ _ _ q a b ha hb k
    (by rw [← Category.assoc, ha, hk])

private theorem triple_base2 (p : A.space ⟶ S) :
    p2 p ≫ p = p1 p ≫ p := by
  dsimp only [p1, p2]
  rw [Category.assoc, Category.assoc, pullback.condition]

private theorem triple_base3 (p : A.space ⟶ S) :
    p3 p ≫ p = p1 p ≫ p := by
  calc
    _ = (p13 p ≫ snd p) ≫ p := by rw [p13_snd]
    _ = (p13 p ≫ fst p) ≫ p := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    _ = _ := by rw [p13_fst]

/-- The corrected atlas overlap satisfies the actual triple-overlap cocycle. -/
theorem overlap_cocycle (P : RelativePinnedComparison.{u}) :
    Descent.Cocycle (A.overlap P) := by
  change (pullIso (p12 A.projection) rfl rfl (A.overlap P)).hom ≫
      (pullIso (p23 A.projection) (p23_fst A.projection) rfl (A.overlap P)).hom =
    (pullIso (p13 A.projection) (p13_fst A.projection)
      (p13_snd A.projection) (A.overlap P)).hom
  rw [A.overlap_pull P (p12 A.projection) _ _ rfl rfl _ rfl,
    A.overlap_pull P (p23 A.projection) _ _ (p23_fst A.projection) rfl _
      (triple_base2 A A.projection),
    A.overlap_pull P (p13 A.projection) _ _ (p13_fst A.projection)
      (p13_snd A.projection) _ rfl]
  exact (congrArg Iso.hom (A.actualTransition_trans P _ _ _ _ rfl
    (triple_base2 A A.projection) (triple_base3 A A.projection))).symm

/-- The actual descent datum built from a supplied natural pinning correction. -/
def datum (P : RelativePinnedComparison.{u}) : Datum A.projection A.group where
  overlap := A.overlap P
  cocycle := A.overlap_cocycle P

end Langlands.GroupScheme.AffinePinnedAtlas
