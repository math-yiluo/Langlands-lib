import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityStatement
import Langlands.Representation.Exponents.Chambers

/-! Blockwise closed cones for actual upper generalized tempered exponents. -/

noncomputable section

open scoped BigOperators

namespace Langlands.Exponents

open GeneralLinear Geometric MeasureTheory

universe uF uV

/-- A supplied real part of an actual generalized upper refined exponent of an
analytically tempered product Levi lies in each scalar and diagonal closed cone. -/
def RefinedUpperTemperedConeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (C : BlockShape n),
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsTemperedModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
        (∀ j : Fin C.length, IsClosedPositiveRootCone
          (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩))) ∧
        (∀ j : Fin C.length, IsClosedPositiveRootCone
          (fun a : Fin (C.size j) =>
            x (C.flattenBlockEquiv D ⟨j, blockIndex (D j) a⟩) /
              ((D j).size (blockIndex (D j) a) : ℝ)))

end Langlands.Exponents
