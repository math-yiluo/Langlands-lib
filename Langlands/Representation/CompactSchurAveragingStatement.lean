import Mathlib.RepresentationTheory.Irreducible
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Averaging conjugated endomorphisms of an irreducible compact representation -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Representation

open MeasureTheory

/-- The dimension times the average of a conjugated endomorphism is its trace
times the identity, for a continuous irreducible complex compact representation. -/
def CompactSchurAveragingStatement (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] : Prop :=
  ∀ (d : ℕ) (ρ : _root_.Representation ℂ G (Fin d → ℂ)),
    Continuous (fun p : G × (Fin d → ℂ) => ρ p.1 p.2) →
    ρ.IsIrreducible →
    ∀ (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
      (T : Module.End ℂ (Fin d → ℂ)) (v : Fin d → ℂ),
      (d : ℂ) • (∫ k : G, ρ k (T (ρ k⁻¹ v)) ∂ν) =
        Matrix.trace (LinearMap.toMatrix' T) • v

end Langlands.Representation
