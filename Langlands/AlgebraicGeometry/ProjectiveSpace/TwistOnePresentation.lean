import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesProof
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

/-! # The projective presentation of the degree-one twist -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The native coordinate sections of the degree-one twist give the identity presentation
of projective space over its base. -/
def twistOneProjPresentation (R : Type u) [CommRing R] (m : ℕ) :
    (twistOne R m).ProjPresentation (projectiveSpaceToSpec R m) m where
  σ := twistOneCoordinate R m
  toProj := 𝟙 _
  toProj_π := Category.id_comp _
  frame i _ hV :=
    ProjTwist.bijective_smul_restrict_section (projectiveSpace_X_mem R m i) hV
  app_ratio_smul i j := (twistOneCoordinate_restrict_coordinateOpen R m i j).symm

/-- The actual degree-one twist is invertible. -/
theorem twistOne_isInvertible (R : Type u) [CommRing R] (m : ℕ) :
    Scheme.Modules.IsInvertibleFLT (twistOne R m) :=
  Picard.isInvertible_of_isLocallyFreeRankOne (projectiveSpaceTwistOneLocalFrames R m).2

/-- The native sections of `𝒪(1)` give a closed immersion over the affine base. -/
theorem twistOne_closedImmersionBySections (R : Type u) [CommRing R] (m : ℕ) :
    Scheme.Modules.ClosedImmersionBySections (twistOne R m) (projectiveSpaceToSpec R m) :=
  ⟨m, twistOneProjPresentation R m, by
    change IsClosedImmersion (𝟙 (ProjectiveSpace R m))
    infer_instance⟩

end Langlands.AlgebraicGeometry
