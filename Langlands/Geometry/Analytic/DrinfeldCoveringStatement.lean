import Langlands.Geometry.Analytic.DrinfeldBuildingCovering
import Langlands.Geometry.Analytic.AnalyticDomainSpaces

/-! # Harris's domains `U(f)` form a distinguished covering of `Ω` with the nerve of the building -/

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open Set

/-- Over a non-Archimedean local field `F`, for all small `ε > 0`, Harris's domains
`U(f) = Res⁻¹(B(f, ε))` of Drinfeld's upper half space `Ω ⊂ ℙ^d_K`:

1. cover `Ω` already for the vertices `f = {e}`;
2. are distinguished for every facet `f`: differences `V \ W` of two compact analytic domains
   of `Ω`;
3. have the building as nerve: for a nonempty finite set `S` of vertices, `U(S)` (the
   intersection of the `U(e)`, `e ∈ S`) is nonempty exactly when `S` is a facet. -/
def DistinguishedCoveringStatement : Prop :=
  ∀ (F : Type v) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra F K] (d : ℕ) [NeZero d],
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (⋃ (e : NormClass F (Fin (d + 1) → F)) (_ : NormClass.IsVertex e),
          facetDomain K {e} ε) = univ ∧
      (∀ S : Set (NormClass F (Fin (d + 1) → F)), NormClass.IsFacet S →
        ∃ V W : (SaturatedAtlasPresentation.ofSaturation (presentation F K d)).AnalyticDomain,
          (SaturatedAtlasPresentation.ofSaturation (presentation F K d)).IsCompactDomain V ∧
          (SaturatedAtlasPresentation.ofSaturation (presentation F K d)).IsCompactDomain W ∧
          facetDomain K S ε = V.carrier \ W.carrier) ∧
      (∀ S : Finset (NormClass F (Fin (d + 1) → F)), S.Nonempty →
        (∀ e ∈ S, NormClass.IsVertex e) →
          ((facetDomain K (S : Set (NormClass F (Fin (d + 1) → F))) ε).Nonempty ↔
            NormClass.IsFacet (S : Set (NormClass F (Fin (d + 1) → F)))))

end Langlands.Analytic.DrinfeldUpperHalfSpace
