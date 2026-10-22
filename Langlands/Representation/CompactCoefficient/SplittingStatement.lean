import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.MatrixCoefficient.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Support

/-!
# Splitting off an irreducible representation with compact matrix coefficients

This is a proposition, not a proof. It is a consequence of Bernstein--Zelevinsky
(1976), Section 2.44(a), with the hypotheses of Section 2.42 retained.
-/

namespace Langlands

open MeasureTheory

universe uG uV uW

/-- Every embedding of a smooth irreducible complex representation with compact
smooth-dual matrix coefficients splits, as does every surjection onto it.
The ambient smooth representation is arbitrary. A regular two-sided Haar
measure makes the unimodularity hypothesis explicit. -/
def CompactCoefficientSplittingStatement
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
    [Measure.IsMulRightInvariant μ] : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    IsSmooth ρ →
    ρ.IsIrreducible →
    (∀ (v : V) (ℓ : Module.Dual ℂ V), IsSmoothVector ρ.dual ℓ →
      HasCompactSupport (matrixCoefficient ρ ℓ v)) →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ G W),
      IsSmooth σ →
      (∀ i : Representation.IntertwiningMap ρ σ, Function.Injective i →
        ∃ r : Representation.IntertwiningMap σ ρ,
          r.comp i = Representation.IntertwiningMap.id ρ) ∧
      (∀ p : Representation.IntertwiningMap σ ρ, Function.Surjective p →
        ∃ s : Representation.IntertwiningMap ρ σ,
          p.comp s = Representation.IntertwiningMap.id ρ)

end Langlands
