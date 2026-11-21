import Langlands.Geometry.Analytic.QuasiEtaleCompactProbeTopology

/-! # Compact-probe covering sieves on Hausdorff quasi-étale objects -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set Topology

/-- At each point of the target, finitely many chart images of arrows of the
presieve have union a neighbourhood (Berkovich 1994, §3, p. 544). -/
def HasQuasiEtaleChartNeighborhoods {K : Type u} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {X : LocalizedCategory.{u, v, v} (K := K)}
    {U : QuasiEtaleSite X} (R : Presieve U) : Prop :=
  ∀ x : localizedSpaceFunctor.obj U.left,
    ∃ σ : Set (Set (localizedSpaceFunctor.obj U.left)), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 x ∧
      ∀ T ∈ σ, ∃ (V : QuasiEtaleSite X) (f : V ⟶ U)
        (i : (presentationOf V.left).presentation.atlas.Index),
        R f ∧ T = localizedSpaceFunctor.map f.left ''
          ((presentationOf V.left).chartDomain i).carrier

/-- On a Hausdorff object of `QuasiEtaleSite X`, the compact-probe test for a
sieve is equivalent to the chart-image neighbourhood condition. The base `X`
need not be Hausdorff. -/
def CompactProbeQuasiEtaleHausdorffComparisonStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (X : LocalizedCategory.{u, v, v} (K := K)) (U : QuasiEtaleSite X) (S : Sieve U),
    T2Space (localizedSpaceFunctor.obj U.left) →
      (S ∈ compactProbeQuasiEtaleTopology X U ↔ HasQuasiEtaleChartNeighborhoods S.arrows)

end Langlands.Analytic.SaturatedAtlasPresentation
