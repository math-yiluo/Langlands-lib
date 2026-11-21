import Langlands.Geometry.Analytic.QuasiEtaleCompactProbeTopology

/-! # Finite compact refinements for the compact-probe quasi-étale topology -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

/-- Every covering sieve on a compact Hausdorff quasi-étale site object has a
finite family of arrows with compact Hausdorff sources that generates a
covering sieve for the compact-probe topology. -/
def CompactProbeQuasiEtaleCompactRefinementsStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (X : LocalizedCategory.{u, v, v} (K := K)) ⦃U : QuasiEtaleSite X⦄,
    IsCompactSpace U.left → ∀ ⦃S : Sieve U⦄, S ∈ compactProbeQuasiEtaleTopology X U →
      ∃ (n : ℕ) (V : Fin n → QuasiEtaleSite X) (f : ∀ i, V i ⟶ U),
        (∀ i, IsCompactSpace (V i).left) ∧ (∀ i, S (f i)) ∧
          Sieve.ofArrows V f ∈ compactProbeQuasiEtaleTopology X U

end Langlands.Analytic.SaturatedAtlasPresentation
