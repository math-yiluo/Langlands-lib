import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.CocharacterTransport

/-! # Pullback evaluation components and canonical descent -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.EmbeddingProduct

section Schemes

variable {B S T : Scheme.{u}}
    (b : S ⟶ B) (l : T ⟶ B) (t : T ⟶ S) (ht : t ≫ b = l)
    (W : GroupScheme B)

/-- The canonical map from one scalar extension to an intermediate one. -/
def intermediateProjection :
    ((GroupScheme.baseChange l).obj W).X.left ⟶
      ((GroupScheme.baseChange b).obj W).X.left :=
  pullback.lift (pullback.fst W.X.hom l) (pullback.snd W.X.hom l ≫ t)
    (by rw [Category.assoc, ht, pullback.condition])

@[reassoc (attr := simp)] theorem intermediateProjection_fst :
    intermediateProjection b l t ht W ≫ pullback.fst W.X.hom b =
      pullback.fst W.X.hom l :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem intermediateProjection_snd :
    intermediateProjection b l t ht W ≫ pullback.snd W.X.hom b =
      pullback.snd W.X.hom l ≫ t :=
  pullback.lift_snd _ _ _

/-- Direct/iterated base-change comparison induces the canonical intermediate projection. -/
theorem pullbackComparison_inv_intermediateProjection :
    (Descent.pullbackComparison b t l ht W).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange b).obj W).X.hom t =
      intermediateProjection b l t ht W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Descent.pullbackComparison_inv_fst,
      intermediateProjection_fst]
  · have hw := Over.w (Descent.pullbackComparison b t l ht W).inv.hom.hom
    change (Descent.pullbackComparison b t l ht W).inv.hom.hom.left ≫
      pullback.snd (pullback.snd W.X.hom b) t = pullback.snd W.X.hom l at hw
    change (Descent.pullbackComparison b t l ht W).inv.hom.hom.left ≫
      pullback.fst (pullback.snd W.X.hom b) t ≫ pullback.snd W.X.hom b = _
    rw [pullback.condition, ← Category.assoc, hw, intermediateProjection_snd]

variable (a : T ⟶ T) (ha : a ≫ l = l) (t' : T ⟶ S)
    (ht' : t' ≫ b = l) (hat : a ≫ t = t')

include hat in
/-- Canonical descent preserves the original intermediate projection. -/
theorem intermediateProjection_descent :
    (descentBaseChangeIso l a ha W).hom.hom.hom.left ≫
        intermediateProjection b l t' ht' W =
      pullback.fst ((GroupScheme.baseChange l).obj W).X.hom a ≫
        intermediateProjection b l t ht W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, intermediateProjection_fst]
    change _ = pullback.fst (pullback.snd W.X.hom l) a ≫ pullback.fst W.X.hom l
    exact descentBaseChangeIso_hom_fst l a ha W
  · simp only [Category.assoc, intermediateProjection_snd]
    have hw := Over.w (descentBaseChangeIso l a ha W).hom.hom.hom
    change (descentBaseChangeIso l a ha W).hom.hom.hom.left ≫
      pullback.snd W.X.hom l = pullback.snd (pullback.snd W.X.hom l) a at hw
    change _ = pullback.fst (pullback.snd W.X.hom l) a ≫
      pullback.snd W.X.hom l ≫ t
    rw [← Category.assoc, hw, ← hat]
    exact (pullback.condition_assoc (f := pullback.snd W.X.hom l) (g := a) t).symm

variable (H : GroupScheme S)
    (e : (GroupScheme.baseChange b).obj W ⟶ H)

/-- The actual base change of one original evaluation map, in direct coordinates. -/
def evaluationComponent :
    (GroupScheme.baseChange l).obj W ⟶ (GroupScheme.baseChange t).obj H :=
  (Descent.pullbackComparison b t l ht W).inv ≫
    (GroupScheme.baseChange t).map e

@[reassoc] theorem evaluationComponent_fst :
    (evaluationComponent b l t ht W H e).hom.hom.left ≫ pullback.fst H.X.hom t =
      intermediateProjection b l t ht W ≫ e.hom.hom.left := by
  have he : ((GroupScheme.baseChange t).map e).hom.hom.left ≫
      pullback.fst H.X.hom t =
    pullback.fst ((GroupScheme.baseChange b).obj W).X.hom t ≫ e.hom.hom.left :=
      pullback.lift_fst _ _ _
  simp only [evaluationComponent, Grp.comp_hom_hom, Over.comp_left, Category.assoc, he]
  rw [← Category.assoc, pullbackComparison_inv_intermediateProjection]

/-- Pulling an original evaluation map back commutes with canonical descent. -/
theorem evaluationComponent_descent :
    (GroupScheme.baseChange a).map (evaluationComponent b l t ht W H e) ≫
        (Descent.pullbackComparison t a t' hat H).hom =
      (descentBaseChangeIso l a ha W).hom ≫
        evaluationComponent b l t' ht' W H e := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Descent.pullbackComparison_hom_fst, evaluationComponent_fst]
    change _ ≫ pullback.fst ((GroupScheme.baseChange t).obj H).X.hom a ≫
      pullback.fst H.X.hom t = _
    rw [← Category.assoc,
      show ((GroupScheme.baseChange a).map
          (evaluationComponent b l t ht W H e)).hom.hom.left ≫
          pullback.fst ((GroupScheme.baseChange t).obj H).X.hom a =
        pullback.fst ((GroupScheme.baseChange l).obj W).X.hom a ≫
          (evaluationComponent b l t ht W H e).hom.hom.left from
        pullback.lift_fst _ _ _,
      Category.assoc, evaluationComponent_fst, ← Category.assoc,
      ← intermediateProjection_descent b l t ht W a ha t' ht' hat,
      Category.assoc]
  · exact (Over.w ((GroupScheme.baseChange a).map
      (evaluationComponent b l t ht W H e) ≫
        (Descent.pullbackComparison t a t' hat H).hom).hom.hom).trans
      (Over.w ((descentBaseChangeIso l a ha W).hom ≫
        evaluationComponent b l t' ht' W H e).hom.hom).symm

end Schemes

end Langlands.GroupScheme.EmbeddingProduct
