import Langlands.Representation.Classification.ProductLeviSquareIntegrableExponent

/-!
# Square integrability of coefficients from strict fundamental bounds

This internal summation interface retains arbitrary admissible carriers and
every supplied Borel Haar measure on the quotient by the full centre.
-/

namespace Langlands

universe uF uV

/-- The strict fundamental Jacquet bounds imply exponent-two integrability of
every descended absolute coefficient, given the Cartan cell count. -/
def GLProductLeviStrictCoefficientL2Statement : Prop :=
  GeneralLinear.CartanQuotient.CartanCellCountStatement.{uF} →
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
      letI := T.topology
      ∀ (n : ℕ) (C : GeneralLinear.BlockShape n),
        letI := T.leviTopologicalGroup C
        let Q := C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)
        ∀ [MeasurableSpace Q] [BorelSpace Q]
          (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
          (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (C.Levi F.Carrier) V),
          IsAdmissible ρ →
          ProductLeviSquareIntegrable.StrictFundHypothesis T C ρ →
          ∀ (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ) (v : V),
            MeasureTheory.MemLp (c.coefficientNorm ℓ v) 2 μ

end Langlands
