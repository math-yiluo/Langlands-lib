import Langlands.Global.AdelicL2FiniteVectorDensity
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Real Lie derivatives on the canonical adelic quotient -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Archimedean Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Geometry.Manifold Langlands.GroupScheme
  AdelicGroupPoints InfiniteAdelicGroupPoints RestrictionSplitCentre

/-- On the measured quotient, the Lie derivative of a smooth right-regular vector is
represented almost everywhere by the invariant derivative of its smooth slices. -/
def CanonicalL2LieDerivativeStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (d : ℕ) (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    let I := 𝓘(ℝ, smoothModel F d)
    let R := (canonicalL2BoundedRightAction hG).comp (ofInfinite F G).toMonoidHom
    ∀ (w : Lp ℂ 2 (canonicalMeasure F G)) (φ : AdelicGroupPoints F G → ℂ),
      Langlands.Archimedean.IsSmoothVector I R w →
      IsLeftInvariantUnder F G (canonicalRationalSubgroup F G) φ →
      (∀ b, functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G) →
      (w : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G] (fun q => φ q.out) →
      ∀ X : GroupLieAlgebra I (InfiniteAdelicGroupPoints F G),
        ((lieDerivative I R X w : Lp ℂ 2 (canonicalMeasure F G)) : CanonicalQuotient F G → ℂ)
          =ᵐ[canonicalMeasure F G]
          fun q => groupDirectionalValue I X (functionInfiniteSlice F G φ (finite F G q.out))
            (infinite F G q.out)

end Langlands.Global
