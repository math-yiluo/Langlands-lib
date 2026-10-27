import Langlands.Representation.Exponents.WeakCriticalStatement
import Langlands.Representation.Exponents.DualCharacterQuotient

/-! The analytic discrete-series criterion for an irreducible quotient of an
actual maximal central-defect layer. This file states the criterion. -/

namespace Langlands

universe uF uV uW

/-- An irreducible admissible quotient of the actual maximal defect image
of a prescribed weakly critical exponent is square-integrable modulo the
full Levi center for every Borel Haar realization. -/
def GLWeaklyCriticalTopLayerL2Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
        ∀ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
          T.IsWeaklyCriticalDualJacquetExponent (Exponents.ConjugateBlockPair.standard B) A χ →
            ∀ (d : ℕ), 0 < d → T.dualJacquetExponentNilpotenceIndex B A χ = (d : ℕ∞) →
              ∀ (a : Fin B.length → F.Carrierˣ) (S : Rep.{uW} ℂ (B.Levi F.Carrier)),
                Representation.IsIrreducible S.ρ →
                (letI := T.leviTopologicalGroup B
                 IsAdmissible S.ρ) →
                Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ →
                ∀ q : (T.dualJacquetCharacterDefectRangeRepresentation B A χ a (d - 1)).ρ.IntertwiningMap S.ρ,
                  Function.Surjective q →
                  (letI := T.leviTopologicalGroup B
                   let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
                   ∀ [MeasurableSpace Q] [BorelSpace Q]
                     (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
                     IsSquareIntegrableModCenter S.ρ μ)

end Langlands
