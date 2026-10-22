import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Induction.Parabolic
import Mathlib.RepresentationTheory.Semisimple

/-!
# Unitarity and normalized induction of tempered representations

The analytic tempered predicate and the actual normalized induction are
independent constructions. These statements specialize Silberger's unitarity
and complete-reducibility results to GL_n and its actual block Levi groups.
-/

namespace Langlands

universe uF uV

namespace PadicField.TopologicalData

/-- The central quotient of the actual block Levi admits Borel Haar measure. -/
theorem exists_isHaarMeasure_leviCentralQuotient
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    letI := borel (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))
    ∃ μ : MeasureTheory.Measure
        (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)),
      μ.IsHaarMeasure := by
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  have := T.leviLocallyCompactSpace B
  let := borel (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))
  have : BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)) := ⟨rfl⟩
  exact ⟨MeasureTheory.Measure.haarMeasure (Classical.arbitrary _), inferInstance⟩

end PadicField.TopologicalData

/-- Every irreducible analytically tempered GL_n representation admits an
invariant positive definite Hermitian form. -/
def GLTemperedUnitarityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    ∀ (n : ℕ), 0 < n →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
        Representation.IsIrreducible ρ → T.IsTempered ρ → IsUnitarizable ρ

/-- Induction from an irreducible analytically tempered representation of the
actual block Levi is completely reducible and analytically tempered. -/
def GLTemperedInductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ M V),
        Representation.IsIrreducible σ → IsTemperedModCenter σ μ →
          IsUnitarizable σ ∧
          Representation.IsSemisimpleRepresentation (T.normalizedParabolicInduced B σ) ∧
          T.IsTempered (T.normalizedParabolicInduced B σ)

/-- Tempered unitarity and normalized-induction prerequisites for GL_n. -/
def GLTemperedInductionPrerequisitesStatement : Prop :=
  GLTemperedUnitarityStatement.{uF, uV} ∧ GLTemperedInductionStatement.{uF, uV}

end Langlands
