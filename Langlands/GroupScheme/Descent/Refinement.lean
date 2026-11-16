import Langlands.GroupScheme.Descent.Reindex

/-! # Restricting actual Čech descent data along commutative squares -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S C V T : Scheme.{u}}

private theorem square_condition {p : S ⟶ B} (t : V ⟶ C) (q : V ⟶ S)
    (b : C ⟶ B) (w : q ≫ p = t ≫ b)
    (f g : T ⟶ V) (h : f ≫ t = g ≫ t) :
    (f ≫ q) ≫ p = (g ≫ q) ≫ p := by
  simpa only [Category.assoc, w] using congrArg (· ≫ b) h

/-- Reindexing a directly pulled-back homomorphism gives its iterated pullback. -/
@[simp] theorem reindexHom_map (q : V ⟶ S) (f : T ⟶ V)
    {G H : GroupScheme S} (a : G ⟶ H) :
    reindexHom q f f ((baseChange (f ≫ q)).map a) =
      (baseChange f).map ((baseChange q).map a) := by
  apply (cancel_mono (pullbackComparison q f (f ≫ q) rfl H).hom).mp
  simp only [reindexHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (pullbackComparison_naturality q f (f ≫ q) rfl a).symm

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- The actual overlap on a square's upper cover. -/
def reindexOverlap (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) : OverlapIso t ((baseChange q).obj G) :=
  reindexIso q (fst t) (snd t)
    (D.transition (fst t ≫ q) (snd t ≫ q)
      (square_condition t q b w _ _ pullback.condition))

/-- Restriction of the new overlap is the old transition on the restricted endpoints. -/
theorem pullHom_reindexOverlap (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) (a : T ⟶ Overlap t) (r s : T ⟶ V)
    (hr : a ≫ fst t = r) (hs : a ≫ snd t = s) :
    pullHom a hr hs (D.reindexOverlap t q b w).hom =
      reindexHom q r s (D.transition (r ≫ q) (s ≫ q)
        (square_condition t q b w r s
          (by rw [← hr, ← hs, Category.assoc, Category.assoc,
            pullback.condition]))).hom := by
  rw [reindexOverlap, reindexIso_hom, pullHom_reindexHom, pullHom_transition]

/-- Restrict an actual datum along any commutative square. -/
def reindex (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) : Datum t ((baseChange q).obj G) where
  overlap := D.reindexOverlap t q b w
  cocycle := by
    change pullHom (p12 t) rfl rfl _ ≫ pullHom (p23 t) (p23_fst t) rfl _ =
      pullHom (p13 t) (p13_fst t) (p13_snd t) _
    rw [pullHom_reindexOverlap, pullHom_reindexOverlap, pullHom_reindexOverlap,
      ← reindexHom_comp, transition_comp]

/-- The transition of a restricted datum is the reindexed original transition. -/
theorem transition_reindex (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) (f g : T ⟶ V) (h : f ≫ t = g ≫ t) :
    ((D.reindex t q b w).transition f g h).hom =
      reindexHom q f g
        (D.transition (f ≫ q) (g ≫ q) (square_condition t q b w f g h)).hom := by
  change pullHom (pullback.lift f g h) (by simp) (by simp)
    (D.reindexOverlap t q b w).hom = _
  exact D.pullHom_reindexOverlap t q b w _ _ _ _ _

/-- Restrict a cover over its original base. -/
def refine (q : V ⟶ S) : Datum (q ≫ p) ((baseChange q).obj G) :=
  D.reindex (q ≫ p) q (𝟙 B) (by simp)

/-- Pull an actual datum back to any new base scheme. -/
def baseChange (b : C ⟶ B) :
    Datum (pullback.snd p b) ((Langlands.GroupScheme.baseChange
      (pullback.fst p b)).obj G) :=
  D.reindex (pullback.snd p b) (pullback.fst p b) b pullback.condition

end Datum

/-- A compatible homomorphism respects all actual transitions. -/
theorem Compatible.transition {p : S ⟶ B} {G H : GroupScheme S}
    {D : Datum p G} {E : Datum p H} {f : G ⟶ H} (hf : Compatible D E f)
    (a b : T ⟶ S) (h : a ≫ p = b ≫ p) :
    (baseChange a).map f ≫ (E.transition a b h).hom =
      (D.transition a b h).hom ≫ (baseChange b).map f := by
  let l := pullback.lift a b h
  have ha : l ≫ fst p = a := by simp [l]
  have hb : l ≫ snd p = b := by simp [l]
  have hc := congrArg (pullHom l ha hb) hf
  change pullHom l ha hb ((baseChange (fst p)).map f ≫ E.overlap.hom) =
    pullHom l ha hb (D.overlap.hom ≫ (baseChange (snd p)).map f) at hc
  rw [pullHom_comp l ha ha hb, pullHom_comp l ha hb hb,
    pullHom_map, pullHom_map] at hc
  exact hc

/-- Restricting the source and target data preserves compatibility of actual homomorphisms. -/
theorem Compatible.reindex {p : S ⟶ B} {G H : GroupScheme S}
    {D : Datum p G} {E : Datum p H} {f : G ⟶ H} (hf : Compatible D E f)
    (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B) (w : q ≫ p = t ≫ b) :
    Compatible (D.reindex t q b w) (E.reindex t q b w)
      ((baseChange q).map f) := by
  have hc := hf.transition (fst t ≫ q) (snd t ≫ q)
    (square_condition t q b w _ _ pullback.condition)
  have hr := congrArg (reindexHom q (fst t) (snd t)) hc
  rw [reindexHom_comp, reindexHom_comp, reindexHom_map, reindexHom_map] at hr
  exact hr

end Langlands.GroupScheme.Descent
