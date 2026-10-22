import Langlands.Representation.Classification.TemperedInductionStatement
import Langlands.Group.GL.OppositeBlocks
import Langlands.Representation.Jacquet.Normalized
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Discrete-series temperedness and opposite Jacquet quotients

Two GL_n prerequisites from Silberger 1979, Theorem 4.5.10 and the
(1)-(2) equivalence of Theorem 4.5.18. These are proposition definitions.
-/

namespace Langlands
universe uF uV uW

/-- An irreducible square-integrable-mod-center representation of an actual
standard block Levi is analytically tempered for the same Borel Haar measure. -/
def GLLeviDiscreteSeriesTemperedStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopologicalGroup B
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (σ : Representation ℂ M W),
        Representation.IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
          IsTemperedModCenter σ μ

/-- For irreducible tempered GL_n data and irreducible discrete-series Levi
input, occurrence as a subquotient of the actual opposite normalized Jacquet
representation is equivalent to occurrence as its quotient. -/
def GLTemperedDiscreteSeriesJacquetQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopologicalGroup B
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear n F.Carrier) V)
        (σ : Representation ℂ M W),
        Representation.IsIrreducible π → T.IsTempered π →
        Representation.IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
          let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
          let J : Representation ℂ M
              (Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)) :=
            (Jacquet.normalizedActionOfModulus π
            (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
            δ⁻¹).comp (B.leviEquiv F.Carrier).toMonoidHom
          let occurs := ∃ S : Subrepresentation J,
            ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q
          let quotient := ∃ q : J.IntertwiningMap σ, Function.Surjective q
          occurs ↔ quotient

/-- The discrete-series temperedness and opposite Jacquet quotient prerequisites. -/
def GLDiscreteSeriesJacquetPrerequisitesStatement : Prop :=
  GLLeviDiscreteSeriesTemperedStatement.{uF, uW} ∧
  GLTemperedDiscreteSeriesJacquetQuotientStatement.{uF, uV, uW}

end Langlands
