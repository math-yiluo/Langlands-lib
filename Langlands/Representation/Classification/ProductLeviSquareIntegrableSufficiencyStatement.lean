import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyStatement

/-!
# Product-Levi square-integrability from strict Jacquet exponent bounds

Two proposition definitions state Casselman's sufficiency criterion for
square-integrability modulo the full centre of an irreducible admissible
representation of an actual GL block Levi with unitary scalar character.
The core form uses upper generalized Jacquet exponents on blockwise monotone
absolute values; the consumer form uses dual eigenfunctionals on opposite
Jacquet quotients and within-block prefix sums of real parts. They state the
criteria; they do not prove them.
-/

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV

/-- Weak upper generalized-exponent bounds on every refinement, strict whenever
the absolute values are not constant on some block, imply square-integrability
modulo the actual centre of the whole product Levi, for every Borel Haar measure. -/
def GLProductLeviSquareIntegrableExponentSufficiencyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (C : BlockShape n) (S : Rep.{uV} ℂ (C.Levi F.Carrier))
      (ω : (Fin C.length → F.Carrierˣ) →* ℂˣ),
      Representation.IsIrreducible S.ρ → IsAdmissible S.ρ →
      Classification.HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) ω →
      (∀ a, ‖(ω a : ℂ)‖ = 1) →
      (∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet C D S.ρ).comp
            ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
              ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
          (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          ‖(ψ a : ℂ)‖ ≤ 1 ∧
            ((∃ (j : Fin C.length) (i i' : Fin (D j).length),
                T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier) ≠
                  T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i'⟩) : F.Carrier)) →
              ‖(ψ a : ℂ)‖ < 1)) →
      (letI := T.leviTopologicalGroup C
       let Q := C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)
       ∀ [MeasurableSpace Q] [BorelSpace Q]
         (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
         IsSquareIntegrableModCenter S.ρ μ)

/-- Nonpositive within-block prefixes of every opposite Jacquet dual exponent,
strictly negative for every proper prefix, imply square-integrability modulo
the actual centre of the whole product Levi, for every Borel Haar measure. -/
def GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (C : BlockShape n) (S : Rep.{uV} ℂ (C.Levi F.Carrier))
      (ω : (Fin C.length → F.Carrierˣ) →* ℂˣ),
      Representation.IsIrreducible S.ρ → IsAdmissible S.ρ →
      Classification.HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) ω →
      (∀ a, ‖(ω a : ℂ)‖ = 1) →
      (∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ)
        (s : Fin (C.flatten D).length → ℝ)
        (φ : Module.Dual ℂ (RefinedOppositeJacquetModule C D S.ρ)),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) → φ ≠ 0 →
        (∀ (a : Fin (C.flatten D).length → F.Carrierˣ) (v : S),
          φ (T.normalizedRefinedOppositeJacquet C D S.ρ
              (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))
              (refinedOppositeJacquetMk C D S.ρ v)) =
            (ψ a : ℂ) * φ (refinedOppositeJacquetMk C D S.ρ v)) →
        T.IsRealPartOf ψ s →
        ∀ (j : Fin C.length) (i : Fin (D j).length),
          (∑ k ∈ Finset.univ.filter (fun k : Fin (D j).length => k ≤ i),
            s (C.flattenBlockEquiv D ⟨j, k⟩)) ≤ 0 ∧
          ((i : ℕ) + 1 < (D j).length →
            (∑ k ∈ Finset.univ.filter (fun k : Fin (D j).length => k ≤ i),
              s (C.flattenBlockEquiv D ⟨j, k⟩)) < 0)) →
      (letI := T.leviTopologicalGroup C
       let Q := C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)
       ∀ [MeasurableSpace Q] [BorelSpace Q]
         (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
         IsSquareIntegrableModCenter S.ρ μ)

end Langlands
