import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-!
# Positive-root unitary cuspidal support of product-Levi discrete series

The fine-to-middle support step in Silberger 1978, p.99, specialized to actual
standard product Levis of GL_n. This is a proposition definition, not a proof.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Every irreducible analytically square-integrable product-Levi representation
is a quotient of actual upper normalized induction from unitary cuspidal data
with the negative of a strictly positive scalar-root parameter. -/
def GLDiscreteSeriesPositiveRootSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (D : BlockShape n)
      (σ : Rep.{uV} ℂ (D.Levi F.Carrier)),
      Representation.IsIrreducible σ.ρ →
      RelativeRegularComparison.IsLeviSquareIntegrable T D σ →
      ∃ (R : BlockRefinement D)
        (ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier))
        (v₀ : Fin (D.flatten R).length → ℝ),
        Representation.IsIrreducible ω.ρ ∧
        CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ ∧
        IsUnitarizable ω.ρ ∧
        RelativeRegularComparison.IsPositiveRootParameter D R v₀ ∧
        ∃ q : (RelativeJacquetMultiplicity.innerInduced T D R
          (RelativeJacquetMultiplicity.fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ,
          Function.Surjective q

end Langlands
