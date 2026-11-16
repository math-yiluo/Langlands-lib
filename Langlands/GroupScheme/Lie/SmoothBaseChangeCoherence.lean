import Langlands.GroupScheme.Lie.SmoothBaseChange
import Langlands.GroupScheme.Lie.CotangentBaseChangeCoherence

/-! # Base-map coherence for the actual smooth Lie comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S T U : AlgebraicGeometry.Scheme.{u}}

/-- Smoothness of a group scheme is preserved by arbitrary base change. -/
lemma smooth_baseChange_of_smooth (b : T ⟶ S) (G : GroupScheme S)
    (hG : Smooth G.X.hom) : Smooth ((baseChange b).obj G).X.hom := by
  let := hG
  change Smooth (Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The sequential actual Lie comparison for two base maps. -/
def smoothLieBaseChangeCompIso (b : T ⟶ S) (c : U ⟶ T) (G : GroupScheme S)
    (hG : Smooth G.X.hom) :
    (pullback c).obj ((pullback b).obj G.Lie) ≅
      ((baseChange c).obj ((baseChange b).obj G)).Lie :=
  (pullback c).mapIso (smoothLieBaseChangeIso b G hG) ≪≫
    smoothLieBaseChangeIso c ((baseChange b).obj G) (smooth_baseChange_of_smooth b G hG)

/-- Identity base change becomes the module identity comparison after applying
the differential of the actual group identity comparison. -/
@[reassoc]
theorem smoothLieBaseChangeIso_id (G : GroupScheme S) (hG : Smooth G.X.hom) :
    (smoothLieBaseChangeIso (𝟙 S) G hG).hom ≫ lieMap (baseChangeIdIso G).hom =
      (pullbackId S).hom.app G.Lie := by
  apply (cancel_mono (dualMap ((pullbackId S).hom.app G.cotangentAtIdentity))).mp
  change ((smoothLieBaseChangeIso (𝟙 S) G hG).hom ≫
    dualMap (cotangentMap (baseChangeIdIso G).hom)) ≫
      dualMap ((pullbackId S).hom.app G.cotangentAtIdentity) = _
  rw [Category.assoc, ← dualMap_comp, ← cotangentBaseChangeMap_id,
    smoothLieBaseChangeIso_characterization, dualPullbackComparison_id]
  rfl

/-- The dual comparison composition formula with forward module comparisons. -/
private lemma dualPullbackComparison_comp_hom (b : T ⟶ S) (c : U ⟶ T)
    (M : S.Modules) :
    (pullback c).map (dualPullbackComparison b M) ≫
        dualPullbackComparison c ((pullback b).obj M) =
      (pullbackComp c b).hom.app (dual M) ≫
        dualPullbackComparison (c ≫ b) M ≫
          dualMap ((pullbackComp c b).hom.app M) := by
  rw [dualPullbackComparison_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← dualMap_comp,
    Iso.hom_inv_id_app, dualMap_id]
  change _ = (pullback c).map (dualPullbackComparison b M) ≫
    dualPullbackComparison c ((pullback b).obj M) ≫ 𝟙 _
  rw [Category.comp_id]

/-- Sequential Lie base change agrees with the comparison for the composite
after the differential of the actual group composition comparison. -/
@[reassoc]
theorem smoothLieBaseChangeIso_comp (b : T ⟶ S) (c : U ⟶ T) (G : GroupScheme S)
    (hG : Smooth G.X.hom) (hGb : Smooth ((baseChange b).obj G).X.hom) :
    (pullback c).map (smoothLieBaseChangeIso b G hG).hom ≫
        (smoothLieBaseChangeIso c ((baseChange b).obj G) hGb).hom ≫
          lieMap (baseChangeCompIso b c G).inv =
      (pullbackComp c b).hom.app G.Lie ≫
        (smoothLieBaseChangeIso (c ≫ b) G hG).hom := by
  let : IsIso (cotangentBaseChangeMap (c ≫ b) G) :=
    cotangentBaseChangeIsIso S U (c ≫ b) G
  have hd := congrArg (fun k => dualMap k) (cotangentBaseChangeMap_comp b c G)
  simp only [dualMap_comp] at hd
  change dualMap (cotangentBaseChangeMap c ((baseChange b).obj G)) ≫
      dualMap ((pullback c).map (cotangentBaseChangeMap b G)) =
    lieMap (baseChangeCompIso b c G).inv ≫
      dualMap (cotangentBaseChangeMap (c ≫ b) G) ≫
        dualMap ((pullbackComp c b).hom.app G.cotangentAtIdentity) at hd
  apply (cancel_mono (dualMap (cotangentBaseChangeMap (c ≫ b) G) ≫
    dualMap ((pullbackComp c b).hom.app G.cotangentAtIdentity))).mp
  simp only [Category.assoc]
  rw [← hd, smoothLieBaseChangeIso_characterization_assoc c ((baseChange b).obj G) hGb,
    ← dualPullbackComparison_naturality c (cotangentBaseChangeMap b G),
    ← Functor.map_comp_assoc, smoothLieBaseChangeIso_characterization,
    smoothLieBaseChangeIso_characterization_assoc]
  exact dualPullbackComparison_comp_hom b c G.cotangentAtIdentity

/-- The sequential comparison itself equals the canonical composite-base route. -/
theorem smoothLieBaseChangeCompIso_hom (b : T ⟶ S) (c : U ⟶ T)
    (G : GroupScheme S) (hG : Smooth G.X.hom) :
    (smoothLieBaseChangeCompIso b c G hG).hom =
      (pullbackComp c b).hom.app G.Lie ≫
        (smoothLieBaseChangeIso (c ≫ b) G hG).hom ≫
          lieMap (baseChangeCompIso b c G).hom := by
  have h := smoothLieBaseChangeIso_comp b c G hG (smooth_baseChange_of_smooth b G hG)
  have hi : lieMap (baseChangeCompIso b c G).hom ≫
      lieMap (baseChangeCompIso b c G).inv = 𝟙 _ := by
    rw [← lieMap_comp, Iso.hom_inv_id, lieMap_id]
  let : IsIso (lieMap (baseChangeCompIso b c G).inv) :=
    (lieFunctor U).map_isIso (baseChangeCompIso b c G).inv
  apply (cancel_mono (lieMap (baseChangeCompIso b c G).inv)).mp
  simpa only [smoothLieBaseChangeCompIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, hi, Category.comp_id] using h

end Langlands.GroupScheme
