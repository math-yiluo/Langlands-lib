import Langlands.Geometry.Analytic.FullRecognitionFiniteFieldPointLifting
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof

/-! # Full field-point lifts for locally finite analytic maps -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation} {y : A.space}

/-- A chosen full field point over a prescribed target field point, at a
specified source point where the actual saturated map is finite. -/
def IsFiniteAt.fieldPointLift (hg : g.IsFiniteAt y)
    (p : FieldPoint L B.saturatedPresentation) (hp : p.point = g.baseMap y) :
    FieldPoint L A.saturatedPresentation :=
  Classical.choose (hg.hasFieldPointLiftAt
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity p hp)

/-- The chosen lift lies at the specified ordinary source point. -/
theorem IsFiniteAt.fieldPointLift_point (hg : g.IsFiniteAt y)
    (p : FieldPoint L B.saturatedPresentation) (hp : p.point = g.baseMap y) :
    (hg.fieldPointLift p hp).point = y :=
  (Classical.choose_spec (hg.hasFieldPointLiftAt
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity p hp)).1

/-- The image is the entire prescribed target field point, including all
chart evaluations and their compatibility. -/
theorem IsFiniteAt.fieldPointLift_map (hg : g.IsFiniteAt y)
    (p : FieldPoint L B.saturatedPresentation) (hp : p.point = g.baseMap y) :
    (hg.fieldPointLift p hp).map g A.atlas.saturatedAtlas_hasAllLocalDomains = p :=
  (Classical.choose_spec (hg.hasFieldPointLiftAt
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity p hp)).2

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Every full field point whose ordinary point is in the image of an
all-pieces etale strong map has a full field-point preimage. -/
theorem strongEtaleFieldPointImageLift :
    StrongEtaleFieldPointImageLiftStatement.{u, v, uL} :=
  strongEtaleFieldPointImageLift_of_domain
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity

end Langlands.Analytic.SaturatedAtlasPresentation
