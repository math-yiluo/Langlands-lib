import Langlands.Representation.Exponents.DualJacquet
import Langlands.Representation.Classification.TemperedSupportStatement
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Finite dual exponents and tempered class exponents

These proposition definitions use actual opposite Jacquet subquotients.
They assert finiteness and comparison results; they do not prove them.
-/

namespace Langlands

universe uF uV uW

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The Jacquet realization of a class exponent: an irreducible admissible
representation occurring as an actual subquotient of the normalized opposite
Jacquet module. The carrier of the constituent is independent of the source. -/
def IsOppositeJacquetClassExponent
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (S : Rep.{uW} ℂ (B.Levi F.Carrier)) : Prop :=
  letI := T.topology
  Representation.IsIrreducible S.ρ ∧ IsAdmissible S.ρ ∧
    ∃ U : Subrepresentation (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ,
      ∃ q : U.toRepresentation.IntertwiningMap S.ρ, Function.Surjective q

end PadicField.TopologicalData

/-- The dual spectrum of an irreducible admissible representation is finite,
every occurring component has a finite uniform nilpotence order, and these
actual generalized components span the full algebraic dual. -/
def GLDualJacquetFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → IsAdmissible A.ρ →
        {χ | T.IsDualJacquetExponent B A χ}.Finite ∧
        (∀ χ, T.IsDualJacquetExponent B A χ →
          T.dualJacquetExponentNilpotenceIndex B A χ < ⊤) ∧
        (⨆ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
            (_ : T.IsDualJacquetExponent B A χ),
          (generalizedCommutativeCharacterSpace
            (T.splitCentreDualJacquet B A).ρ χ).toSubmodule) = ⊤

/-- A dual exponent occurs exactly when it is the scalar split-center
character of an irreducible admissible opposite Jacquet constituent. -/
def GLDualJacquetClassExponentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → IsAdmissible A.ρ →
        ∀ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
          T.IsDualJacquetExponent B A χ ↔
            ∃ S : Rep.{uV} ℂ (B.Levi F.Carrier),
              T.IsOppositeJacquetClassExponent B A S ∧
              Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ

/-- For a tempered source, an irreducible admissible opposite Jacquet
constituent is analytically tempered exactly when its split-center character
is unitary. This compares two predicates rather than defining them equal. -/
def GLTemperedJacquetClassExponentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopologicalGroup B
      let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
        Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
          ∀ (S : Rep.{uW} ℂ (B.Levi F.Carrier))
            (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
            T.IsOppositeJacquetClassExponent B A S →
            Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ →
              (IsTemperedModCenter S.ρ μ ↔ ∀ a, ‖(χ a : ℂ)‖ = 1)

/-- Every unitary dual exponent of a tempered irreducible representation
supports an embedding into opposite normalized induction from a tempered
irreducible Levi representation with that prescribed split-center character. -/
def GLUnitaryDualJacquetTemperedSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
        ∀ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
          T.IsUnitaryDualJacquetExponent B A χ →
            ∃ S : Rep.{uV} ℂ (B.Levi F.Carrier),
              T.IsOppositeJacquetClassExponent B A S ∧
              Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ ∧
              (letI := T.leviTopologicalGroup B
               let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
               ∀ [MeasurableSpace Q] [BorelSpace Q]
                 (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
                 IsTemperedModCenter S.ρ μ) ∧
              ∃ j : A.ρ.IntertwiningMap (T.normalizedOppositeParabolicInduced B S.ρ),
                Function.Injective j

/-- The finite-spectrum, class-exponent and weak-exponent comparison family. -/
def GLDualJacquetExponentPrerequisitesStatement : Prop :=
  GLDualJacquetFinitenessStatement.{uF, uV} ∧
  GLDualJacquetClassExponentStatement.{uF, uV} ∧
  GLTemperedJacquetClassExponentStatement.{uF, uV, uW} ∧
  GLUnitaryDualJacquetTemperedSupportStatement.{uF, uV}

end Langlands
