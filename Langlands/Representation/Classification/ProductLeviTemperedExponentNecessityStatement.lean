import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# Necessary upper Jacquet bounds for an analytically tempered product Levi

This proposition retains the single supplied Borel Haar measure on the actual
full-centre quotient. Its conclusion is the upper generalized-exponent
hypothesis of `GLProductLeviTemperedExponentSufficiencyStatement`.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Analytic temperedness for one Borel Haar measure on the actual product-Levi
central quotient forces every upper refined generalized exponent to have norm
at most one on the chamber increasing separately inside each outer block. -/
def GLProductLeviTemperedExponentNecessityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : BlockShape n,
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ M V),
        Representation.IsIrreducible σ → IsTemperedModCenter σ μ →
        ∀ (D : BlockRefinement B)
          (ψ : (Fin (B.flatten D).length → F.Carrierˣ) →* ℂˣ),
          IsOpen (ψ.ker : Set (Fin (B.flatten D).length → F.Carrierˣ)) →
          IsGeneralizedEigencharacter
            ((T.normalizedRefinedJacquet B D σ).comp
              ((flattenedLeviEquiv F.Carrier B D).toMonoidHom.comp
                ((B.flatten D).blockScalarLevi F.Carrier))) ψ →
          ∀ a : Fin (B.flatten D).length → F.Carrierˣ,
            (∀ j : Fin B.length, Monotone (fun i : Fin (D j).length =>
              T.normalizedAbs (a (B.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
            ‖(ψ a : ℂ)‖ ≤ 1

end Langlands
