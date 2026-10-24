import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Classification.TemperedInductionStatement

/-!
# All-regular relative comparison with discrete-series support

The supported GL_n form of the multiplicity equality in the proof of
Silberger 1978, Lemma 5.6, together with its irreducible-head conclusion.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV uM uW

namespace RelativeRegularComparison

/-- A strictly positive combination of the adjacent scalar roots inside each
middle block, expressed in fine determinant-exponent coordinates. -/
def IsPositiveRootParameter {n : ℕ} (D : BlockShape n) (R : BlockRefinement D)
    (v₀ : Fin (D.flatten R).length → ℝ) : Prop :=
  ∃ c : (i : Fin D.length) → Fin ((R i).length - 1) → ℝ,
    (∀ i j, 0 < c i j) ∧
    ∀ (i : Fin D.length) (k : Fin (R i).length),
      v₀ (D.flattenBlockEquiv R ⟨i, k⟩) =
        ∑ j : Fin ((R i).length - 1), c i j *
          ((if k.val = j.val then (1 : ℝ) / (R i).size k else 0) -
            (if k.val = j.val + 1 then (1 : ℝ) / (R i).size k else 0))

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Analytic discrete series on the whole product Levi, with every Borel Haar
measure on its actual central quotient. Irreducibility is a separate premise. -/
def IsLeviSquareIntegrable (σ : Rep.{uM} ℂ (B.Levi F.Carrier)) : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  ∀ [MeasurableSpace Z] [BorelSpace Z]
    (μ : MeasureTheory.Measure Z) [MeasureTheory.Measure.IsHaarMeasure μ],
    IsSquareIntegrableModCenter σ.ρ μ

/-- Analytic temperedness on the whole product Levi, with every Borel Haar
measure on its actual central quotient. -/
def IsLeviTempered (σ : Rep.{uW} ℂ (B.Levi F.Carrier)) : Prop :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  ∀ [MeasurableSpace Z] [BorelSpace Z]
    (μ : MeasureTheory.Measure Z) [MeasureTheory.Measure.IsHaarMeasure μ],
    IsTemperedModCenter σ.ρ μ

/-- Untwisted normalized induction from a flattened product Levi, using its
constructed identification with the actual refined subgroup. -/
def middleInduced (Q : BlockRefinement B)
    (σ : Rep.{uM} ℂ ((B.flatten Q).Levi F.Carrier)) :
    Rep.{max uF uM} ℂ (B.Levi F.Carrier) :=
  RelativeJacquetMultiplicity.innerInduced T B Q
    (Rep.of (σ.ρ.comp (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom))

end RelativeRegularComparison

open RelativeJacquetMultiplicity RelativeRegularComparison

/-- Supported all-regular relative Jacquet multiplicity equality and the
irreducible head of the actual outer standard module. -/
def GLRelativeRegularComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (Q : BlockRefinement B),
      let D := B.flatten Q
      ∀ (R : BlockRefinement D) (S : BlockRefinement B)
        (h : D.flatten R = B.flatten S)
        (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)),
        Representation.IsIrreducible ω.ρ →
        CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ →
        IsUnitarizable ω.ρ →
        ∀ v₀ : Fin (D.flatten R).length → ℝ,
          IsPositiveRootParameter D R v₀ →
          let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
          let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
          ∀ σ : Rep.{uM} ℂ (D.Levi F.Carrier),
            Representation.IsIrreducible σ.ρ → IsLeviSquareIntegrable T D σ →
            (∃ q : (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ,
              Function.Surjective q) →
            ∀ π : Rep.{uW} ℂ (B.Levi F.Carrier),
              Representation.IsIrreducible π.ρ → IsLeviTempered T B π →
              (∃ q : (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ,
                Function.Surjective q) →
              (∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap π.ρ,
                Function.Surjective q) →
              ∀ t : Fin B.length → ℝ, StrictAnti t →
                let τ := fineTwist T B S ωB vB t
                let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
                ∃ m : ℕ, 0 < m ∧
                  HasJordanHolderMultiplicity (innerJacquet T B S πt) τ m ∧
                  HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ m ∧
                  Classification.HasIrreducibleHead
                    (CuspidalJacquetMultiplicity.induced T B πt).ρ

end Langlands
