import Langlands.Representation.Classification.TemperedInductionStatement
import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Group.GL.OppositeBlocks
import Langlands.Representation.Jacquet.Normalized
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Discrete-series support and summands of tempered representations

These proposition definitions use the published opposite-induction construction.
The Jacquet action below uses the opposite unipotent subgroup and the inverse
upper modulus, transported from the embedded Levi to the product Levi.
-/

namespace Langlands

universe uF uV uW

/-- The existence clause of Silberger's discrete-series support corollary,
specialized to actual standard block parabolics of GL_n. -/
def GLTemperedDiscreteSeriesSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (GeneralLinear n F.Carrier) V),
        Representation.IsIrreducible π → T.IsTempered π →
          ∃ (B : GeneralLinear.BlockShape n)
            (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W)
            (σ : Representation ℂ (B.Levi F.Carrier) W),
            Representation.IsIrreducible σ ∧
            (letI := T.leviTopologicalGroup B
             let Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
             ∀ [MeasurableSpace Q] [BorelSpace Q]
               (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ],
               IsSquareIntegrableModCenter σ μ) ∧
            ∃ j : π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ),
              Function.Injective j

/-- A discrete-series Levi representation occurs in the opposite normalized
Jacquet module exactly when the original tempered representation splits off
both opposite normalized inductions. The quotient equivalence is stated
separately in DiscreteSeriesJacquetStatement. -/
def GLTemperedDiscreteSeriesSummandStatement : Prop :=
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
          let Iupper := T.normalizedParabolicInduced B σ
          let Iopposite := T.normalizedOppositeParabolicInduced B σ
          let summands :=
            Representation.IsSemisimpleRepresentation Iupper ∧
            Representation.IsSemisimpleRepresentation Iopposite ∧
            (∃ (j : π.IntertwiningMap Iupper) (r : Iupper.IntertwiningMap π),
              r.comp j = Representation.IntertwiningMap.id π) ∧
            (∃ (j : π.IntertwiningMap Iopposite) (r : Iopposite.IntertwiningMap π),
              r.comp j = Representation.IntertwiningMap.id π)
          occurs ↔ summands

/-- Discrete-series support and the opposite-induction summand equivalences. -/
def GLTemperedDiscreteSeriesPrerequisitesStatement : Prop :=
  GLTemperedDiscreteSeriesSupportStatement.{uF, uV} ∧
  GLTemperedDiscreteSeriesSummandStatement.{uF, uV, uW}

end Langlands
