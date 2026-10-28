import Langlands.Representation.Classification.TemperedInductionStatement
import Mathlib.RepresentationTheory.Irreducible

/-!
# Discrete-series coefficients of block Levis below exponent two

A derived GL_n prerequisite isolated from the proof of Waldspurger 2003,
Corollary III.1.2: the strict exponent bound used there makes every absolute
coefficient of an irreducible square-integrable-mod-center representation of
an actual standard block Levi lie in `L^r` of the central quotient for some
`r < 2`. This is a proposition definition.
-/

namespace Langlands
universe uF uW

/-- For an irreducible square-integrable-mod-center representation `σ` of an
actual standard block Levi, every absolute matrix coefficient on the actual
central quotient lies in `L^r` for some real exponent `1 < r < 2`, for every
supplied unitary central character. -/
def GLProductLeviSquareIntegrableLpStatement : Prop :=
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
          ∀ (c : UnitaryCentralCharacter σ) (ℓ : SmoothDual σ) (w : W),
            ∃ r : ℝ, 1 < r ∧ r < 2 ∧
              MeasureTheory.MemLp (c.coefficientNorm ℓ w) (ENNReal.ofReal r) μ

end Langlands
