import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# Strict upper cones for square-integrable product-Levi refinements

For one supplied Borel Haar measure on the full central quotient, square
integrability forces every supplied scalar real part of an upper refined
Jacquet exponent into the positive root cone separately in each original block.
This closed proposition is a derived statement and supplies no proof.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric

universe uF uV

/-- Strict blockwise upper refined Jacquet cones for an arbitrary representation
square-integrable modulo the full centre with respect to one supplied Haar
measure. The scalar real parts have separate zero sums and strictly positive
proper prefixes in the original inner ordering. -/
def RefinedUpperSquareIntegrableConeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ C : BlockShape n,
      letI := T.leviTopologicalGroup C
      let M := C.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ M V),
        IsSquareIntegrableModCenter σ μ →
        ∀ (R : BlockRefinement C)
          (χ : (Fin (C.flatten R).length → F.Carrierˣ) →* ℂˣ),
          IsOpen (χ.ker : Set (Fin (C.flatten R).length → F.Carrierˣ)) →
          IsGeneralizedEigencharacter
            ((T.normalizedRefinedJacquet C R σ).comp
              ((flattenedLeviEquiv F.Carrier C R).toMonoidHom.comp
                ((C.flatten R).blockScalarLevi F.Carrier))) χ →
          ∀ x : Fin (C.flatten R).length → ℝ, T.IsRealPartOf χ x →
            ∀ i : Fin C.length,
              IsPositiveRootCone
                (fun k : Fin (R i).length => x (C.flattenBlockEquiv R ⟨i, k⟩))

end Langlands.Exponents
