import Langlands.HarmonicAnalysis.Distribution.SupportedRestriction

/-!
# Local open-restriction criterion for support of algebraic distributions

An internal interface on the published Schwartz–Bruhat subspace maps: an
algebraic distribution whose open restriction vanishes near every point
outside a subset `Z` annihilates every test function vanishing on `Z`.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe u

/-- For every Hausdorff, locally compact, totally disconnected space `X`, every
subset `Z ⊆ X` (not assumed closed) and every algebraic distribution `D` on `X`:
if each point `x ∉ Z` has an open neighborhood `U` such that the open
restriction `restrictOpen hU D` is zero, then `D ∈ supportedOn Z`, that is,
`D f = 0` for every test function `f` with `f z = 0` for all `z ∈ Z`. -/
def OpenRestrictionLocalityStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (Z : Set X) (D : Distribution X),
    (∀ x ∉ Z, ∃ (U : Set X) (hU : IsOpen U),
      x ∈ U ∧ restrictOpen hU D = 0) →
    D ∈ supportedOn Z

end Langlands.HarmonicAnalysis.Distribution
