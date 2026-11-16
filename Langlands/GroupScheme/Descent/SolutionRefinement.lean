import Langlands.GroupScheme.Descent.Refinement
import Langlands.GroupScheme.Descent.SquareSemilinear

/-! # Restricting actual descent solutions -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S C V T : Scheme.{u}}

@[reassoc] private theorem map_fst (a : V ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange a).map f).hom.hom.left ≫ pullback.fst H.X.hom a =
      pullback.fst G.X.hom a ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Every transition of a canonical datum preserves the original projection. -/
@[reassoc] theorem canonicalDatum_transition_fst (p : S ⟶ B) (K : GroupScheme B)
    (f g : T ⟶ S) (h : f ≫ p = g ≫ p) :
    ((canonicalDatum p K).transition f g h).hom.hom.hom.left ≫
        pullback.fst ((baseChange p).obj K).X.hom g ≫ pullback.fst K.X.hom p =
      pullback.fst ((baseChange p).obj K).X.hom f ≫ pullback.fst K.X.hom p :=
  pullHom_canonicalOverlap_fst p K (pullback.lift f g h) f g (by simp) (by simp)

/-- The restricted canonical overlap preserves the original projection. -/
@[reassoc] theorem canonicalDatum_reindexOverlap_fst
    (p : S ⟶ B) (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) (K : GroupScheme B) :
    ((canonicalDatum p K).reindexOverlap t q b w).hom.hom.hom.left ≫
        pullback.fst ((baseChange q).obj ((baseChange p).obj K)).X.hom (snd t) ≫
          pullback.fst ((baseChange p).obj K).X.hom q ≫ pullback.fst K.X.hom p =
      pullback.fst ((baseChange q).obj ((baseChange p).obj K)).X.hom (fst t) ≫
        pullback.fst ((baseChange p).obj K).X.hom q ≫ pullback.fst K.X.hom p := by
  simp only [Datum.reindexOverlap, reindexIso_hom, reindexHom,
    Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    pullbackComparison_inv_fst_assoc, canonicalDatum_transition_fst,
    pullbackComparison_hom_fst_assoc]

/-- The square comparison is compatible with the canonical and restricted canonical data. -/
theorem squareComparison_compatible
    (p : S ⟶ B) (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) (K : GroupScheme B) :
    Compatible (canonicalDatum t ((baseChange b).obj K))
      ((canonicalDatum p K).reindex t q b w)
      (squareComparison b t p q w.symm K).hom := by
  let c := pullbackComparison p q (q ≫ p) rfl K
  apply (cancel_mono ((baseChange (snd t)).mapIso c).hom).mp
  apply hom_ext_pullback_tower (q ≫ p) (snd t) K
  dsimp only [c]
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    Functor.mapIso_hom, map_fst_assoc, pullbackComparison_hom_fst]
  change
    ((baseChange (fst t)).map (squareComparison b t p q w.symm K).hom).hom.hom.left ≫
        ((canonicalDatum p K).reindexOverlap t q b w).hom.hom.hom.left ≫
          pullback.fst ((baseChange q).obj ((baseChange p).obj K)).X.hom (snd t) ≫
            pullback.fst ((baseChange p).obj K).X.hom q ≫
              pullback.fst K.X.hom p =
      (canonicalOverlap t ((baseChange b).obj K)).hom.hom.hom.left ≫
        pullback.fst ((baseChange t).obj ((baseChange b).obj K)).X.hom (snd t) ≫
          (squareComparison b t p q w.symm K).hom.hom.hom.left ≫
            pullback.fst ((baseChange p).obj K).X.hom q ≫ pullback.fst K.X.hom p
  rw [canonicalDatum_reindexOverlap_fst, map_fst_assoc,
    squareComparison_hom_fst_fst, canonicalOverlap_fst_assoc]

namespace Solution

variable {p : S ⟶ B} {G : GroupScheme S} {D : Datum p G} (s : Solution D)

/-- Restrict a supplied solution along a commutative square. -/
def reindex (t : V ⟶ C) (q : V ⟶ S) (b : C ⟶ B)
    (w : q ≫ p = t ≫ b) : Solution (D.reindex t q b w) where
  obj := (baseChange b).obj s.obj
  iso := squareComparison b t p q w.symm s.obj ≪≫ (baseChange q).mapIso s.iso
  compatible :=
    (squareComparison_compatible p t q b w s.obj).comp (s.compatible.reindex t q b w)

/-- Restrict a supplied solution to a refinement of its cover. -/
def refine (q : V ⟶ S) : Solution (D.refine q) :=
  s.reindex (q ≫ p) q (𝟙 B) (by simp)

/-- Restrict a supplied solution to a base change of its cover. -/
def baseChange (b : C ⟶ B) : Solution (D.baseChange b) :=
  s.reindex (pullback.snd p b) (pullback.fst p b) b pullback.condition

end Solution
end Langlands.GroupScheme.Descent
