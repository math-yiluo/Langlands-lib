import Langlands.Geometry.Analytic.DrinfeldBuildingCovering
import Langlands.Geometry.Analytic.AnalyticDomainSpaces

/-! # Harris's domains `U(f)` of Drinfeld's upper half space are distinguished -/

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

/-- Over a non-Archimedean local field `F`, for all small `ε > 0` and every facet `f` of the
building, Harris's domain `U(f) = Res⁻¹(B(f, ε))` of Drinfeld's upper half space `Ω` is
distinguished in Berkovich's sense: the difference `V \ W` of two compact analytic domains of
`Ω`. -/
def FacetDomainDistinguishedStatement : Prop :=
  ∀ (F : Type v) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra F K] (d : ℕ) [NeZero d],
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ S : Set (NormClass F (Fin (d + 1) → F)), NormClass.IsFacet S →
        ∃ V W : (SaturatedAtlasPresentation.ofSaturation (presentation F K d)).AnalyticDomain,
          (SaturatedAtlasPresentation.ofSaturation (presentation F K d)).IsCompactDomain V ∧
          (SaturatedAtlasPresentation.ofSaturation (presentation F K d)).IsCompactDomain W ∧
          facetDomain K S ε = V.carrier \ W.carrier

end Langlands.Analytic.DrinfeldUpperHalfSpace
