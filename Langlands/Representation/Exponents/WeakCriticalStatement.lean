import Langlands.Representation.Exponents.WeakCritical
import Langlands.Representation.Exponents.DualJacquetStatement

/-! Prescribed weakly critical discrete-series support and pair minimality.
These are proposition definitions, not proofs of the representation theory. -/

namespace Langlands

universe uF uV

open Exponents

/-- Weakly minimal standard pairs exist for an irreducible tempered source. -/
def GLWeaklyMinimalStandardPairExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ A : Rep.{uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
        ∃ B : GeneralLinear.BlockShape n,
          T.IsWeaklyMinimalDualJacquetPair (ConjugateBlockPair.standard B) A

/-- A prescribed weakly critical exponent at a standard pair is the scalar
character of discrete-series opposite-inducing data containing the source. -/
def GLWeaklyCriticalDiscreteSeriesSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
        ∀ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
          T.IsWeaklyCriticalDualJacquetExponent (ConjugateBlockPair.standard B) A χ →
            ∃ S : Rep.{uV} ℂ (B.Levi F.Carrier),
              T.IsOppositeJacquetClassExponent B A S ∧
              Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ ∧
              (letI := T.leviTopologicalGroup B
               let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
               ∀ [MeasurableSpace Q] [BorelSpace Q]
                 (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
                 IsSquareIntegrableModCenter S.ρ μ) ∧
              ∃ j : A.ρ.IntertwiningMap (T.normalizedOppositeParabolicInduced B S.ρ),
                Function.Injective j

/-- For a tempered irreducible source, criticality and minimality agree
for every concrete conjugate pair. The converse direction is substantive. -/
def GLWeaklyCriticalPairMinimalityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (P : ConjugateBlockPair n F.Carrier)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
        (T.IsWeaklyCriticalDualJacquetPair P A ↔
          T.IsWeaklyMinimalDualJacquetPair P A)

/-- The weakly critical refinement of tempered discrete-series support. -/
def GLWeaklyCriticalTemperedRefinementStatement : Prop :=
  GLWeaklyMinimalStandardPairExistenceStatement.{uF, uV} ∧
  GLWeaklyCriticalDiscreteSeriesSupportStatement.{uF, uV} ∧
  GLWeaklyCriticalPairMinimalityStatement.{uF, uV}

end Langlands
