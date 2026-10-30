import Langlands.HarmonicAnalysis.Distribution.SupportedRestriction

/-!
# Scalar covariance of supported descent through an open subspace

An internal consequence sought from the published actual descent
`descendInOpen`: compatible homeomorphisms of the ambient space, an open
subspace and the relatively closed nested subtype transfer scalar covariance
of a supported distribution to its chosen descended distribution.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe u

/-- For every Hausdorff, locally compact, totally disconnected space `X`, open
`U ⊆ X` and subset `Z ⊆ X` whose preimage in `U` is closed in `U`, and every
distribution `D` annihilating the test functions vanishing on `Z`: if
homeomorphisms `e` of `X`, `eU` of `U` and `eZ` of the nested subtype commute
with both inclusions and `e_* D = c • D`, then the chosen descent
`descendInOpen hU hZU D` satisfies `eZ_* (descendInOpen hU hZU D) =
c • descendInOpen hU hZU D`. -/
def SupportedDescentCovarianceStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] (U Z : Set X) (hU : IsOpen U)
    (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z))
    (D : supportedOn Z)
    (e : X ≃ₜ X) (eU : U ≃ₜ U)
    (eZ : ((Subtype.val : U → X) ⁻¹' Z) ≃ₜ ((Subtype.val : U → X) ⁻¹' Z))
    (c : ℂ),
    (∀ x : U, (eU x).val = e x.val) →
    (∀ z : ((Subtype.val : U → X) ⁻¹' Z), (eZ z).val = eU z.val) →
    pushforward e (D : Distribution X) = c • (D : Distribution X) →
    pushforward eZ (descendInOpen hU hZU D) = c • descendInOpen hU hZU D

end Langlands.HarmonicAnalysis.Distribution
