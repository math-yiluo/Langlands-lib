import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityStatement

/-!
# Necessary strict upper Jacquet bounds for square-integrable product Levis

The analytic input is square integrability for one supplied Borel Haar measure
on the actual quotient by the full centre. The conclusion covers the whole
blockwise chamber and is strict away from the blockwise central directions.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Square integrability modulo the full centre forces the weak upper refined
Jacquet bound on the whole blockwise chamber, and the strict bound whenever the
absolute values are nonconstant within at least one outer block. -/
def GLProductLeviSquareIntegrableExponentNecessityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : BlockShape n,
      letI := T.leviTopologicalGroup B
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ M V),
        IsSquareIntegrableModCenter σ μ →
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
            ‖(ψ a : ℂ)‖ ≤ 1 ∧
              ((∃ (j : Fin B.length) (i k : Fin (D j).length),
                T.normalizedAbs (a (B.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier) ≠
                  T.normalizedAbs (a (B.flattenBlockEquiv D ⟨j, k⟩) : F.Carrier)) →
                ‖(ψ a : ℂ)‖ < 1)

end Langlands
