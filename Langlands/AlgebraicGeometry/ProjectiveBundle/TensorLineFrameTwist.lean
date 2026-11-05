import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineTwistGluing

/-! # Tensor-line degree one on the fixed projective frame bundles -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

/-- The fixed tensor bundle carries the pulled-back source degree one times the base line. -/
abbrev frameSourceTensorTwistModule :
    (frameBundle (tensorObj M N) n (isLocallyFreeOfRank_tensor hM hN)).Modules :=
  tensorObj ((Scheme.Modules.pullback (frameBundleIso hM hN).hom).obj
    (FrameBundle.twistOne hM).obj)
      ((Scheme.Modules.pullback (FrameBundle.toBase
        (isLocallyFreeOfRank_tensor hM hN))).obj N)

/-- The inverse tensor-atlas comparison identifies the source degree-one pullbacks. -/
def sourceTwistToFrameIso :
    (Scheme.Modules.pullback
      ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).inv).obj
        ((Scheme.Modules.pullback (atlasIso hM hN).hom).obj
          ((sourceAtlas hM hN).twistOne hM).obj) ≅
      (Scheme.Modules.pullback (frameBundleIso hM hN).hom).obj
        (FrameBundle.twistOne hM).obj :=
  compIso
      ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).inv
      (atlasIso hM hN).hom
      (((tensorAtlas hM hN).toFrameBundleIso
        (isLocallyFreeOfRank_tensor hM hN)).inv ≫ (atlasIso hM hN).hom)
      rfl ((sourceAtlas hM hN).twistOne hM).obj ≪≫
    compIso
      (((tensorAtlas hM hN).toFrameBundleIso
        (isLocallyFreeOfRank_tensor hM hN)).inv ≫ (atlasIso hM hN).hom)
      ((sourceAtlas hM hN).toFrameBundleIso hM).hom
      (frameBundleIso hM hN).hom
      (by simp only [frameBundleIso, Iso.trans_hom, Iso.symm_hom, Category.assoc])
      (FrameBundle.twistOne hM).obj

/-- The inverse tensor-atlas comparison transports the entire tensor module. -/
def sourceTensorTwistToFrameIso :
    (Scheme.Modules.pullback
      ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).inv).obj
        (sourceTensorTwistModule hM hN) ≅ frameSourceTensorTwistModule hM hN := by
  let f := ((tensorAtlas hM hN).toFrameBundleIso
    (isLocallyFreeOfRank_tensor hM hN)).inv
  letI := pullbackTensorComparisonIsIso f
  exact (asIso (pullbackTensorComparison f)).app
      ((Scheme.Modules.pullback (atlasIso hM hN).hom).obj
        ((sourceAtlas hM hN).twistOne hM).obj,
        (Scheme.Modules.pullback (tensorAtlas hM hN).toBase).obj N) ≪≫
    (Langlands.Scheme.Modules.tensorFunctor _).mapIso
      ((sourceTwistToFrameIso hM hN).prod
        (compIso f (tensorAtlas hM hN).toBase
          (FrameBundle.toBase (isLocallyFreeOfRank_tensor hM hN))
          ((tensorAtlas hM hN).toFrameBundleIso_inv_toBase
            (isLocallyFreeOfRank_tensor hM hN)) N))

/-- The tensor-line degree-one comparison on the fixed projective frame bundles. -/
def frameBundleTwistIso :
    (FrameBundle.twistOne (isLocallyFreeOfRank_tensor hM hN)).obj ≅
      frameSourceTensorTwistModule hM hN :=
  (compIso
      ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).inv
      ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).hom
      (𝟙 _) (Iso.inv_hom_id _)
      (FrameBundle.twistOne (isLocallyFreeOfRank_tensor hM hN)).obj ≪≫
    (Scheme.Modules.pullbackId _).app
      (FrameBundle.twistOne (isLocallyFreeOfRank_tensor hM hN)).obj).symm ≪≫
    (Scheme.Modules.pullback
      ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).inv).mapIso
        (tensorLineTwistIso hM hN) ≪≫ sourceTensorTwistToFrameIso hM hN

/-- The same comparison in the category of actual line bundles. -/
def frameBundleTwistLineIso :
    FrameBundle.twistOne (isLocallyFreeOfRank_tensor hM hN) ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        ((LineBundle.pullback (frameBundleIso hM hN).hom).obj
          (FrameBundle.twistOne hM))
        ((LineBundle.pullback
          (FrameBundle.toBase (isLocallyFreeOfRank_tensor hM hN))).obj ⟨N, hN⟩) :=
  ObjectProperty.isoMk _ (frameBundleTwistIso hM hN)

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
