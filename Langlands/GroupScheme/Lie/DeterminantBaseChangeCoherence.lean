import Langlands.GroupScheme.Lie.DeterminantLineBundle
import Langlands.GroupScheme.Lie.SmoothBaseChangeCoherence

/-! # Base-map coherence for actual smooth Lie determinant lines -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S T U : Scheme.{u}}

/-- Identity base change of the actual Lie determinant is the canonical
line-bundle identity comparison. -/
lemma smoothLieDeterminantBaseChangeIso_identity
    (G : GroupScheme S) (hG : Smooth G.X.hom) :
    smoothLieDeterminantBaseChangeIso (𝟙 S) G hG ≪≫
        smoothLieDeterminantIso (smooth_baseChange_of_smooth (𝟙 S) G hG) hG
          (baseChangeIdIso G) =
      (LineBundle.pullbackId S).app (smoothLieDeterminant G hG) := by
  have hi : smoothLieBaseChangeIso (𝟙 S) G hG ≪≫
        (lieFunctor S).mapIso (baseChangeIdIso G) =
      (Scheme.Modules.pullbackId S).app G.Lie := by
    apply Iso.ext
    exact smoothLieBaseChangeIso_id G hG
  dsimp only [smoothLieDeterminantBaseChangeIso, smoothLieDeterminantIso]
  rw [Iso.trans_assoc, finiteLocallyFreeDeterminantIso_comp, hi]
  exact finiteLocallyFreeDeterminantPullbackIso_identity (G.lie_hasFiniteLocalBasis hG)

/-- The successive canonical base-change comparison of actual Lie determinant lines. -/
def smoothLieDeterminantBaseChangeCompIso
    (b : T ⟶ S) (c : U ⟶ T) (G : GroupScheme S) (hG : Smooth G.X.hom) :
    (LineBundle.pullback c).obj ((LineBundle.pullback b).obj
        (smoothLieDeterminant G hG)) ≅
      smoothLieDeterminant ((baseChange c).obj ((baseChange b).obj G))
        (smooth_baseChange_of_smooth c ((baseChange b).obj G)
          (smooth_baseChange_of_smooth b G hG)) :=
  (LineBundle.pullback c).mapIso (smoothLieDeterminantBaseChangeIso b G hG) ≪≫
    smoothLieDeterminantBaseChangeIso c ((baseChange b).obj G)
      (smooth_baseChange_of_smooth b G hG)

/-- Sequential base change of the actual Lie determinant agrees with the
composite base change and the canonical group and module comparisons. -/
lemma smoothLieDeterminantBaseChangeIso_composition
    (b : T ⟶ S) (c : U ⟶ T) (G : GroupScheme S) (hG : Smooth G.X.hom) :
    (LineBundle.pullback c).mapIso (smoothLieDeterminantBaseChangeIso b G hG) ≪≫
        smoothLieDeterminantBaseChangeIso c ((baseChange b).obj G)
          (smooth_baseChange_of_smooth b G hG) ≪≫
        smoothLieDeterminantIso
          (smooth_baseChange_of_smooth c ((baseChange b).obj G)
            (smooth_baseChange_of_smooth b G hG))
          (smooth_baseChange_of_smooth (c ≫ b) G hG) (baseChangeCompIso b c G).symm =
      (LineBundle.pullbackComp c b).app (smoothLieDeterminant G hG) ≪≫
        smoothLieDeterminantBaseChangeIso (c ≫ b) G hG := by
  have hc : (Scheme.Modules.pullback c).mapIso (smoothLieBaseChangeIso b G hG) ≪≫
        smoothLieBaseChangeIso c ((baseChange b).obj G)
          (smooth_baseChange_of_smooth b G hG) ≪≫
        (lieFunctor U).mapIso (baseChangeCompIso b c G).symm =
      (Scheme.Modules.pullbackComp c b).app G.Lie ≪≫
        smoothLieBaseChangeIso (c ≫ b) G hG := by
    apply Iso.ext
    exact smoothLieBaseChangeIso_comp b c G hG (smooth_baseChange_of_smooth b G hG)
  dsimp only [smoothLieDeterminantBaseChangeIso, smoothLieDeterminantIso]
  rw [Functor.mapIso_trans]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc
    ((LineBundle.pullback c).mapIso
      (finiteLocallyFreeDeterminantIso
        (HasFiniteLocalBasis.pullback (G.lie_hasFiniteLocalBasis hG) b)
        (((baseChange b).obj G).lie_hasFiniteLocalBasis
          (smooth_baseChange_of_smooth b G hG))
        (smoothLieBaseChangeIso b G hG))),
    finiteLocallyFreeDeterminantPullbackIso_naturality]
  simp only [Iso.trans_assoc, finiteLocallyFreeDeterminantIso_comp]
  rw [hc, ← finiteLocallyFreeDeterminantIso_comp
    (HasFiniteLocalBasis.pullback
      (HasFiniteLocalBasis.pullback (G.lie_hasFiniteLocalBasis hG) b) c)
    (HasFiniteLocalBasis.pullback (G.lie_hasFiniteLocalBasis hG) (c ≫ b))
    (((baseChange (c ≫ b)).obj G).lie_hasFiniteLocalBasis
      (smooth_baseChange_of_smooth (c ≫ b) G hG))]
  simpa only [Iso.trans_assoc, smoothLieDeterminant] using congrArg
    (fun e => e ≪≫ finiteLocallyFreeDeterminantIso
      (HasFiniteLocalBasis.pullback (G.lie_hasFiniteLocalBasis hG) (c ≫ b))
      (((baseChange (c ≫ b)).obj G).lie_hasFiniteLocalBasis
        (smooth_baseChange_of_smooth (c ≫ b) G hG))
      (smoothLieBaseChangeIso (c ≫ b) G hG))
    (finiteLocallyFreeDeterminantPullbackIso_composition
      (G.lie_hasFiniteLocalBasis hG) c b)

end Langlands.GroupScheme
