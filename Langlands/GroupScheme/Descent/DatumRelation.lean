import Langlands.GroupScheme.Descent.Data

/-! # The all-test relation of an actual Čech datum -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {B S T U Z : Scheme.{u}}

@[reassoc] private theorem map_fst (q : U ⟶ T) {G H : GroupScheme T} (a : G ⟶ H) :
    ((baseChange q).map a).hom.hom.left ≫ pullback.fst H.X.hom q =
      pullback.fst G.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Evaluate a pulled morphism on a test scheme using the original morphism. -/
theorem pullHom_eval (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hr : q ≫ f = r) (hs : q ≫ g = s) {G H : GroupScheme S}
    (e : (baseChange f).obj G ⟶ (baseChange g).obj H)
    (a : Z ⟶ G.X.left) (z : Z ⟶ U) (ha : a ≫ G.X.hom = z ≫ r) :
    pullback.lift a z ha ≫ (pullHom q hr hs e).hom.hom.left ≫
        pullback.fst H.X.hom s =
      pullback.lift a (z ≫ q) (by rw [Category.assoc, hr]; exact ha) ≫
        e.hom.hom.left ≫ pullback.fst H.X.hom g := by
  have hc : pullback.lift a z ha ≫
        (pullbackComparison f q r hr G).inv.hom.hom.left ≫
        pullback.fst ((baseChange f).obj G).X.hom q =
      pullback.lift a (z ≫ q) (by rw [Category.assoc, hr]; exact ha) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackComparison_inv_fst, pullback.lift_fst]
    · have hw := Over.w (pullbackComparison f q r hr G).inv.hom.hom
      change (pullbackComparison f q r hr G).inv.hom.hom.left ≫
          pullback.snd ((baseChange f).obj G).X.hom q = pullback.snd G.X.hom r at hw
      simp only [Category.assoc, pullback.lift_snd]
      change pullback.lift a z ha ≫
        (pullbackComparison f q r hr G).inv.hom.hom.left ≫
        pullback.fst ((baseChange f).obj G).X.hom q ≫ ((baseChange f).obj G).X.hom = z ≫ q
      simp only [pullback.condition, reassoc_of% hw,
        pullback.lift_snd_assoc]
  simp only [pullHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    pullbackComparison_hom_fst, map_fst_assoc, reassoc_of% hc]

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- The overlap point recording an original base coordinate and a new one. -/
def pointOverlap (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) : Z ⟶ Overlap p :=
  pullback.lift (a ≫ G.X.hom) b h

/-- Transport an arbitrary test-scheme point along the actual overlap isomorphism. -/
def move (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) : Z ⟶ G.X.left :=
  pullback.lift a (pointOverlap a b h) (by simp [pointOverlap]) ≫
    D.overlap.hom.hom.hom.left ≫ pullback.fst G.X.hom (snd p)

@[reassoc] theorem move_base (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) :
    D.move a b h ≫ G.X.hom = b := by
  have hw := Over.w D.overlap.hom.hom.hom
  change D.overlap.hom.hom.hom.left ≫ pullback.snd G.X.hom (snd p) =
    pullback.snd G.X.hom (fst p) at hw
  simp only [move, Category.assoc, pullback.condition, reassoc_of% hw,
    pullback.lift_snd_assoc, pointOverlap, pullback.lift_snd]

private theorem point_compatible (q : U ⟶ Overlap p) {r s : U ⟶ S}
    (hr : q ≫ fst p = r) (hs : q ≫ snd p = s)
    (a : Z ⟶ G.X.left) (z : Z ⟶ U) (ha : a ≫ G.X.hom = z ≫ r) :
    a ≫ G.X.hom ≫ p = (z ≫ s) ≫ p := by
  rw [reassoc_of% ha, Category.assoc]
  apply congrArg (fun k => z ≫ k)
  rw [← hr, ← hs, Category.assoc, Category.assoc, pullback.condition]

/-- The direct-pullback expression of transport agrees with point transport. -/
@[reassoc] theorem pullHom_move (q : U ⟶ Overlap p) {r s : U ⟶ S}
    (hr : q ≫ fst p = r) (hs : q ≫ snd p = s)
    (a : Z ⟶ G.X.left) (z : Z ⟶ U) (ha : a ≫ G.X.hom = z ≫ r) :
    pullback.lift a z ha ≫ (pullHom q hr hs D.overlap.hom).hom.hom.left =
      pullback.lift (D.move a (z ≫ s) (point_compatible q hr hs a z ha)) z (D.move_base _ _ _) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullHom_eval, pullback.lift_fst]
    have hh : pointOverlap a (z ≫ s) (point_compatible q hr hs a z ha) = z ≫ q := by
      apply pullback.hom_ext
      · simpa only [pointOverlap, pullback.lift_fst, Category.assoc, hr] using ha
      · simp only [pointOverlap, pullback.lift_snd, Category.assoc, hs]
    simp only [move, hh]
  · have hw := Over.w (pullHom q hr hs D.overlap.hom).hom.hom
    change (pullHom q hr hs D.overlap.hom).hom.hom.left ≫ pullback.snd G.X.hom s =
      pullback.snd G.X.hom r at hw
    simp only [Category.assoc, hw, pullback.lift_snd]

/-- The cocycle gives successive transport on every test scheme. -/
theorem move_move (a : Z ⟶ G.X.left) (b c : Z ⟶ S)
    (hab : a ≫ G.X.hom ≫ p = b ≫ p) (hbc : b ≫ p = c ≫ p) :
    D.move (D.move a b hab) c (by rw [D.move_base_assoc]; exact hbc) =
      D.move a c (hab.trans hbc) := by
  let r12 : Z ⟶ Overlap p := pointOverlap a b hab
  let r23 : Z ⟶ Overlap p := pullback.lift b c hbc
  let z : Z ⟶ Triple p := pullback.lift r12 r23 (by simp [r12, r23, pointOverlap])
  have hz1 : z ≫ p1 p = a ≫ G.X.hom := by simp [z, p1, p12, r12, pointOverlap]
  have hz2 : z ≫ p2 p = b := by simp [z, p2, p12, r12, pointOverlap]
  have hz3 : z ≫ p3 p = c := by simp [z, p3, p23, r23]
  have hc := congrArg (fun e => pullback.lift a z hz1.symm ≫
    e.hom.hom.left ≫ pullback.fst G.X.hom (p3 p)) D.cocycle
  change pullback.lift a z hz1.symm ≫
      ((iso12 D.overlap).hom.hom.hom.left ≫ (iso23 D.overlap).hom.hom.hom.left) ≫ _ =
    pullback.lift a z hz1.symm ≫ (iso13 D.overlap).hom.hom.hom.left ≫ _ at hc
  simp only [Category.assoc] at hc
  change pullback.lift a z hz1.symm ≫
      (pullHom (p12 p) rfl rfl D.overlap.hom).hom.hom.left ≫
      (pullHom (p23 p) (p23_fst p) rfl D.overlap.hom).hom.hom.left ≫ _ =
    pullback.lift a z hz1.symm ≫
      (pullHom (p13 p) (p13_fst p) (p13_snd p) D.overlap.hom).hom.hom.left ≫ _ at hc
  rw [D.pullHom_move_assoc, D.pullHom_move_assoc, D.pullHom_move_assoc] at hc
  simpa only [pullback.lift_fst, hz2, hz3] using hc

/-- Transport is injective after fixing both original and new base coordinates. -/
theorem move_injective {a a' : Z ⟶ G.X.left}
    (hbase : a ≫ G.X.hom = a' ≫ G.X.hom) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) (h' : a' ≫ G.X.hom ≫ p = b ≫ p)
    (he : D.move a b h = D.move a' b h') : a = a' := by
  have hr : pointOverlap a b h = pointOverlap a' b h' := by
    apply pullback.hom_ext
    · simpa only [pointOverlap, pullback.lift_fst] using hbase
    · simp only [pointOverlap, pullback.lift_snd]
  have hx : pullback.lift a (pointOverlap a b h) (by simp [pointOverlap]) ≫
        D.overlap.hom.hom.hom.left =
      pullback.lift a' (pointOverlap a' b h') (by simp [pointOverlap]) ≫
        D.overlap.hom.hom.hom.left := by
    apply pullback.hom_ext
    · exact he
    · have hw := Over.w D.overlap.hom.hom.hom
      change D.overlap.hom.hom.hom.left ≫ pullback.snd G.X.hom (snd p) =
        pullback.snd G.X.hom (fst p) at hw
      simpa only [Category.assoc, hw, pullback.lift_snd] using hr
  have hxy := (cancel_mono D.overlap.hom.hom.hom.left).mp hx
  simpa only [Category.assoc, pullback.lift_fst] using
    congrArg (fun x => x ≫ pullback.fst G.X.hom (fst p)) hxy

/-- The cocycle and invertibility force transport on the diagonal to be the identity. -/
@[simp] theorem move_self (a : Z ⟶ G.X.left) :
    D.move a (a ≫ G.X.hom) (Category.assoc _ _ _).symm = a := by
  apply D.move_injective (D.move_base _ _ _) (a ≫ G.X.hom)
  exact D.move_move a (a ≫ G.X.hom) (a ≫ G.X.hom) _ rfl

/-- Transport back to the original base coordinate recovers the point. -/
@[simp] theorem move_back (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) :
    D.move (D.move a b h) (a ≫ G.X.hom) (by
      rw [D.move_base_assoc]; exact h.symm.trans (Category.assoc _ _ _).symm) = a := by
  rw [D.move_move _ _ _ _ (by simpa only [Category.assoc] using h.symm), D.move_self]

/-- The actual relation scheme of the datum. -/
abbrev relationScheme (_D : Datum p G) : Scheme.{u} :=
  ((baseChange (fst p)).obj G).X.left

/-- The original point of a relation arrow. -/
abbrev source (D : Datum p G) : D.relationScheme ⟶ G.X.left :=
  pullback.fst G.X.hom (fst p)

/-- The transported point of a relation arrow. -/
def target : D.relationScheme ⟶ G.X.left :=
  D.overlap.hom.hom.hom.left ≫ pullback.fst G.X.hom (snd p)

/-- The pair of base coordinates attached to a relation arrow. -/
abbrev relationMap (D : Datum p G) : D.relationScheme ⟶ Overlap p :=
  pullback.snd G.X.hom (fst p)

@[reassoc] theorem source_base : D.source ≫ G.X.hom = D.relationMap ≫ fst p :=
  pullback.condition

@[reassoc] theorem target_base : D.target ≫ G.X.hom = D.relationMap ≫ snd p := by
  have hw := Over.w D.overlap.hom.hom.hom
  change D.overlap.hom.hom.hom.left ≫ pullback.snd G.X.hom (snd p) =
    D.relationMap at hw
  simp only [target, Category.assoc, pullback.condition, reassoc_of% hw]

/-- The two endpoints of a relation arrow have the same image in the base. -/
@[reassoc] theorem relation_base : D.source ≫ G.X.hom ≫ p =
    D.target ≫ G.X.hom ≫ p := by
  rw [D.source_base_assoc, D.target_base_assoc, pullback.condition]

/-- The relation arrow taking a point to a specified new base coordinate. -/
def arrow (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) : Z ⟶ D.relationScheme :=
  pullback.lift a (pointOverlap a b h) (by simp [pointOverlap])

@[reassoc (attr := simp)] theorem arrow_source (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) : D.arrow a b h ≫ D.source = a :=
  pullback.lift_fst _ _ _

@[reassoc] theorem arrow_target (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) : D.arrow a b h ≫ D.target = D.move a b h := rfl

/-- Both endpoints determine a relation arrow, on every test scheme. -/
theorem relation_hom_ext {a b : Z ⟶ D.relationScheme}
    (hs : a ≫ D.source = b ≫ D.source) (ht : a ≫ D.target = b ≫ D.target) : a = b := by
  apply pullback.hom_ext
  · exact hs
  · apply pullback.hom_ext
    · simpa only [Category.assoc, ← D.source_base] using congrArg (· ≫ G.X.hom) hs
    · simpa only [Category.assoc, ← D.target_base] using congrArg (· ≫ G.X.hom) ht

/-- The common-base equation for the endpoints of a test-scheme relation arrow. -/
theorem relation_point_base (r : Z ⟶ D.relationScheme) :
    (r ≫ D.source) ≫ G.X.hom ≫ p = (r ≫ D.target ≫ G.X.hom) ≫ p := by
  simpa only [Category.assoc] using congrArg (fun f => r ≫ f) D.relation_base

/-- Reconstruct a relation arrow from its source and target base coordinate. -/
theorem arrow_relation (r : Z ⟶ D.relationScheme) :
    D.arrow (r ≫ D.source) (r ≫ D.target ≫ G.X.hom) (D.relation_point_base r) = r := by
  apply pullback.hom_ext
  · simp only [arrow_source]
  · apply pullback.hom_ext
    · simp only [arrow, pointOverlap, pullback.lift_snd_assoc, pullback.lift_fst,
        Category.assoc, D.source_base]
    · simp only [arrow, pointOverlap, pullback.lift_snd,
        Category.assoc, D.target_base]

/-- An existing relation arrow gives precisely the transported endpoint. -/
@[simp] theorem move_relation (r : Z ⟶ D.relationScheme) :
    D.move (r ≫ D.source) (r ≫ D.target ≫ G.X.hom) (D.relation_point_base r) =
      r ≫ D.target := by
  change D.arrow _ _ _ ≫ D.target = _
  rw [D.arrow_relation]

/-- Every diagonal pair is represented on every test scheme. -/
theorem relation_refl (Z : Scheme.{u}) (a : Z ⟶ G.X.left) :
    ∃ r : Z ⟶ D.relationScheme, r ≫ D.source = a ∧ r ≫ D.target = a := by
  refine ⟨D.arrow a (a ≫ G.X.hom) (Category.assoc _ _ _).symm, by simp, ?_⟩
  rw [D.arrow_target, D.move_self]

/-- Every relation arrow can be reversed on its original test scheme. -/
theorem relation_symm (Z : Scheme.{u}) (r : Z ⟶ D.relationScheme) :
    ∃ r' : Z ⟶ D.relationScheme,
      r' ≫ D.source = r ≫ D.target ∧ r' ≫ D.target = r ≫ D.source := by
  have hback := D.move_back (r ≫ D.source) (r ≫ D.target ≫ G.X.hom)
    (D.relation_point_base r)
  simp only [D.move_relation] at hback
  refine ⟨D.arrow (r ≫ D.target) ((r ≫ D.source) ≫ G.X.hom)
    (by simpa only [Category.assoc] using (D.relation_point_base r).symm), by simp, ?_⟩
  rw [D.arrow_target]
  simpa only [Category.assoc] using hback

/-- Composable relation arrows can be composed on their original test scheme. -/
theorem relation_trans (Z : Scheme.{u}) (r r' : Z ⟶ D.relationScheme)
    (h : r ≫ D.target = r' ≫ D.source) :
    ∃ r'' : Z ⟶ D.relationScheme,
      r'' ≫ D.source = r ≫ D.source ∧ r'' ≫ D.target = r' ≫ D.target := by
  have hbc : (r ≫ D.target ≫ G.X.hom) ≫ p = (r' ≫ D.target ≫ G.X.hom) ≫ p := by
    simpa only [← Category.assoc, h] using D.relation_point_base r'
  have hc := D.move_move (r ≫ D.source) (r ≫ D.target ≫ G.X.hom)
    (r' ≫ D.target ≫ G.X.hom) (D.relation_point_base r) hbc
  simp only [D.move_relation, h] at hc
  refine ⟨D.arrow (r ≫ D.source) (r' ≫ D.target ≫ G.X.hom)
    ((D.relation_point_base r).trans hbc), by simp, ?_⟩
  rw [D.arrow_target]
  exact hc.symm

/-- The endpoint pair is a monomorphism of actual schemes. -/
instance relation_mono : Mono (prod.lift D.source D.target) where
  right_cancellation {Z} a b h := D.relation_hom_ext
    (by simpa only [Category.assoc, prod.lift_fst] using congrArg (· ≫ prod.fst) h)
    (by simpa only [Category.assoc, prod.lift_snd] using congrArg (· ≫ prod.snd) h)

/-- The source square is the original pullback square. -/
theorem source_pullback : IsPullback D.source D.relationMap G.X.hom (fst p) :=
  IsPullback.of_hasPullback _ _

/-- Invertibility of the overlap identification gives the target pullback square. -/
theorem target_pullback : IsPullback D.target D.relationMap G.X.hom (snd p) := by
  let e : D.relationScheme ≅ ((baseChange (snd p)).obj G).X.left :=
    ((Grp.forget (Over (Overlap p))) ⋙ Over.forget (Overlap p)).mapIso D.overlap
  refine (IsPullback.of_hasPullback G.X.hom (snd p)).of_iso e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change pullback.fst G.X.hom (snd p) = e.inv ≫ e.hom ≫ pullback.fst G.X.hom (snd p)
    simp
  · have hw := Over.w D.overlap.inv.hom.hom
    change D.overlap.inv.hom.hom.left ≫ D.relationMap =
      pullback.snd G.X.hom (snd p) at hw
    exact hw.symm
  · simp
  · simp

end Datum
end Langlands.GroupScheme.Descent
