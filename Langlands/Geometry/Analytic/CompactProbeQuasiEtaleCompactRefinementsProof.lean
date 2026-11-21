import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleCompactRefinementsStatement
import Langlands.Geometry.Analytic.CompactQuasiEtalePullbacksProof
import Langlands.Geometry.Analytic.QuasiEtaleRelativePullbackPoints

/-! # Finite compact refinements for the compact-probe quasi-étale topology -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Finite compact refinements are covering by compact pullbacks and point lifting. -/
theorem compactProbeQuasiEtaleCompactRefinements :
    CompactProbeQuasiEtaleCompactRefinementsStatement.{u, v} K := by
  classical
  intro X U hU S hS
  obtain ⟨n, V, f, hV, hf, hsurj⟩ :=
    containsFiniteCompactSurjection_of_mem_compactProbeQuasiEtaleTopology hU hS
  refine ⟨n, V, f, hV, hf, ?_⟩
  intro C g hC
  choose t ht hp using fun i =>
    compactQuasiEtalePullbacks (K := K) X U C (V i) g (f i) hU hC (hV i)
  refine ⟨n, fun i => (t i).pt, fun i => (t i).fst, ht, ?_, ?_⟩
  · intro i
    change Sieve.ofArrows V f ((t i).fst ≫ g)
    rw [(t i).condition]
    exact (Sieve.ofArrows V f).downward_closed (Sieve.ofArrows_mk V f i) (t i).snd
  · intro x
    obtain ⟨i, y, hy⟩ := hsurj ((compactProbePointFunctor X).map g x)
    have hg : quasiEtale (g.left ≫ U.hom) := by
      rw [MorphismProperty.Over.w]
      exact C.prop
    have hxy : localizedSpaceFunctor.map g.left x = localizedSpaceFunctor.map (f i).left y :=
      hy.symm
    obtain ⟨z, hz, _⟩ :=
      exists_point_of_isPullback_over_compactQuasiEtale U.hom (hp i) hg U.prop hU x y hxy
    exact ⟨i, z, hz⟩

end Langlands.Analytic.SaturatedAtlasPresentation
