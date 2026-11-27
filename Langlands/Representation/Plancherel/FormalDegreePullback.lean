import Langlands.Representation.Plancherel.FormalDegreeComparisons
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness

/-! # Transport of formal degree by a measured group isomorphism -/

universe uG uH uV

open MeasureTheory

namespace Langlands.Plancherel

open Langlands.HarishChandraSchwartz

/-- The Schur formal degree is preserved by pullback along an isomorphism
carrying the chosen central subgroup and quotient measure to their counterparts. -/
def RepresentationFormalDegreePullbackStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : H ≃ₜ* G) (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
    (B : Subgroup H) [B.Normal] (hB : B ≤ Subgroup.center H)
    (hAB : B.map e.toMonoidHom = A)
    [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
    [MeasurableSpace (H ⧸ B)] [BorelSpace (H ⧸ B)]
    (μG : Measure (G ⧸ A)) [μG.IsHaarMeasure] [μG.IsInvInvariant]
    (μH : Measure (H ⧸ B)) [μH.IsHaarMeasure] [μH.IsInvInvariant]
    (_hμ : μH.map (quotientContinuousMulEquiv e A B hAB) = μG)
    (hcofG : CompactOpenCofinal G) (hcofH : CompactOpenCofinal H)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : IsSquareIntegrableModCentralSubgroup A hA ρ μG) (hiρ : ρ.IsIrreducible)
    (hσ : IsSquareIntegrableModCentralSubgroup B hB (ρ.comp e.toMonoidHom) μH)
    (hiσ : Representation.IsIrreducible (ρ.comp e.toMonoidHom)),
    representationFormalDegree A hA μG hcofG hρ hiρ =
      representationFormalDegree B hB μH hcofH hσ hiσ

end Langlands.Plancherel
