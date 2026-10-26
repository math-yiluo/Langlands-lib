import Langlands.Representation.Classification.TemperedInductionStatement
import Langlands.Representation.SubrepresentationLattice
import Mathlib.RepresentationTheory.Irreducible

/-!
# Discrete-series isotypic projectors in tempered Levi representations

A derived GL_n prerequisite isolated from the proof of Silberger 1979,
Theorem 4.5.18, which adapts the coefficient-algebra decomposition in the
proof of Theorem 3.3.1 to a tempered module. This is a proposition definition.
-/

namespace Langlands
universe uF uV uW

/-- For an analytically tempered representation `ρ` of an actual standard block
Levi and an irreducible square-integrable-mod-center `σ` with the same exact
scalar central character, the intrinsic `σ`-isotypic subrepresentation, the
supremum of the ranges of all intertwiners `σ → ρ`, is the range of an
idempotent self-intertwiner of `ρ` whose kernel has no subrepresentation with a
surjective intertwiner onto `σ`. -/
def GLTemperedDiscreteSeriesIsotypicStatement : Prop :=
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
        (ρ : Representation ℂ M V) (σ : Representation ℂ M W)
        (cρ : UnitaryCentralCharacter ρ) (cσ : UnitaryCentralCharacter σ),
        IsTemperedModCenter ρ μ →
        Representation.IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
        cρ.character = cσ.character →
          let I : Subrepresentation ρ :=
            ⨆ f : σ.IntertwiningMap ρ, f.range
          ∃ P : ρ.IntertwiningMap ρ, P.comp P = P ∧ P.range = I ∧
            ∀ K : Subrepresentation P.ker.toRepresentation,
              ¬ ∃ q : K.toRepresentation.IntertwiningMap σ, Function.Surjective q

end Langlands
