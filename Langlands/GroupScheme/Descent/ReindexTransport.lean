import Langlands.GroupScheme.Descent.Refinement
import Langlands.GroupScheme.Descent.DatumRelation

/-! # Actual point transport after reindexing a datum -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 2500

namespace Langlands.GroupScheme.Descent

variable {B S C V T Z : Scheme.{u}}

/-- Evaluation of a reindexed morphism preserves its projection to the original group. -/
theorem reindexHom_eval (q : V ⟶ S) (f g : T ⟶ V) {G H : GroupScheme S}
    (e : (baseChange (f ≫ q)).obj G ⟶ (baseChange (g ≫ q)).obj H)
    (a : Z ⟶ ((baseChange q).obj G).X.left) (z : Z ⟶ T)
    (ha : a ≫ ((baseChange q).obj G).X.hom = z ≫ f) :
    pullback.lift a z ha ≫ (reindexHom q f g e).hom.hom.left ≫
        pullback.fst ((baseChange q).obj H).X.hom g ≫ pullback.fst H.X.hom q =
      pullback.lift (a ≫ pullback.fst G.X.hom q) z (by
        rw [Category.assoc, pullback.condition]
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) ha)) ≫
        e.hom.hom.left ≫ pullback.fst H.X.hom (g ≫ q) := by
  have hc : pullback.lift a z ha ≫
        (pullbackComparison q f (f ≫ q) rfl G).hom.hom.hom.left =
      pullback.lift (a ≫ pullback.fst G.X.hom q) z (by
        rw [Category.assoc, pullback.condition]
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) ha)) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackComparison_hom_fst, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · have hw := Over.w (pullbackComparison q f (f ≫ q) rfl G).hom.hom.hom
      change (pullbackComparison q f (f ≫ q) rfl G).hom.hom.hom.left ≫
        pullback.snd G.X.hom (f ≫ q) =
          pullback.snd ((baseChange q).obj G).X.hom f at hw
      simp only [Category.assoc, hw, pullback.lift_snd]
  simp only [reindexHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    pullbackComparison_inv_fst, reassoc_of% hc]

namespace Datum

variable {p : S ⟶ B} {G : GroupScheme S} (D : Datum p G)

/-- Restricting a datum restricts its actual point transport. -/
theorem move_reindex_fst (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b)
    (a : Z ⟶ ((Langlands.GroupScheme.baseChange q).obj G).X.left) (v : Z ⟶ V)
    (h : a ≫ ((Langlands.GroupScheme.baseChange q).obj G).X.hom ≫ t = v ≫ t) :
    (D.reindex t q b w).move a v h ≫ pullback.fst G.X.hom q =
      D.move (a ≫ pullback.fst G.X.hom q) (v ≫ q) (by
        rw [Category.assoc, Category.assoc, pullback.condition_assoc, w]
        have hh := congrArg (· ≫ b) h
        change (a ≫ pullback.snd G.X.hom q ≫ t) ≫ b = (v ≫ t) ≫ b at hh
        simpa only [Category.assoc] using hh) := by
  let z := pointOverlap a v h
  have ha : a ≫ ((Langlands.GroupScheme.baseChange q).obj G).X.hom = z ≫ fst t := by
    simp [z, pointOverlap]
  change pullback.lift a z ha ≫ (D.reindexOverlap t q b w).hom.hom.hom.left ≫
      pullback.fst ((Langlands.GroupScheme.baseChange q).obj G).X.hom (snd t) ≫
      pullback.fst G.X.hom q = _
  rw [reindexOverlap, reindexIso_hom, reindexHom_eval]
  change pullback.lift (a ≫ pullback.fst G.X.hom q) z _ ≫
      (pullHom (pullback.lift (fst t ≫ q) (snd t ≫ q) _)
        (by simp) (by simp) D.overlap.hom).hom.hom.left ≫
      pullback.fst G.X.hom (snd t ≫ q) = _
  rw [pullHom_eval]
  congr 2
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    simp [z, pointOverlap, pullback.condition]
  · simp [z, pointOverlap]

end Datum
end Langlands.GroupScheme.Descent
