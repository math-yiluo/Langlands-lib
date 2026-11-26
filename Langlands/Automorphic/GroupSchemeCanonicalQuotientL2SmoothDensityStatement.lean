import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2SmoothVectors
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Smooth-vector density on the canonical adelic quotient -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme

/-- Both the archimedean smooth vectors and the vectors smooth also at finite level are
dense in `L²([G])` for the canonical measure and right action. -/
def CanonicalQuotientL2SmoothDensityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
    let model := 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension)
    let μQ := canonicalMeasure F G
    let hInv := canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG
    Dense (Langlands.Archimedean.smoothVectors model
      (rationalQuotientL2InfiniteRightAction F G μQ hInv) : Set (Lp ℂ 2 μQ)) ∧
    Dense (rationalQuotientL2BiSmoothVectors F G μQ hInv model : Set (Lp ℂ 2 μQ))

end Langlands.Global.RestrictionSplitCentre
