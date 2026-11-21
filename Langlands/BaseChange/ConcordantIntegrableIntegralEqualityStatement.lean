import Langlands.BaseChange.OrbitalIntegral
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Langlands.BaseChange

open MeasureTheory

/-- The comparison of the two ambient integrals for integrable functions with concordant
orbital integrals. This is the unweighted comparison obtained from the two Weyl formulas. -/
def ConcordantIntegrableIntegralEqualityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (φ : GeneralLinear n E → ℂ) (f : GeneralLinear n F → ℂ),
      Integrable φ μE → Integrable f μF → AreConcordant σ l μF μE φ f →
      (∫ δ, φ δ ∂μE) = ∫ γ, f γ ∂μF

end Langlands.BaseChange
