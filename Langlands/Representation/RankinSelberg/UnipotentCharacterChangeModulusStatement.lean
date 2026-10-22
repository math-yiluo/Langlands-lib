import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.Measures

/-!
# Unipotent Haar measure under character-change conjugation

Conjugation by `d_a = diag(a^n, ..., a, 1)` scales the coordinate `(i,j)` of the
upper-unipotent group by `a^(j-i)`. The proposition below states that the actual
integral-normalized unipotent Haar measure is pushed forward to the reciprocal
modulus times itself. It does not prove that law. The two helper theorems only
show that the pushforward is along a continuous, hence Borel measurable, map.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear Langlands.Whittaker

universe uF

section Helpers

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- Conjugation by the character-change diagonal is continuous on the subgroup. -/
theorem continuous_characterChangeConj (a : Fˣ) (n : ℕ) :
    Continuous (characterChangeConj a n) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- For Borel structures, conjugation by the character-change diagonal is measurable,
so `Measure.map` along it is a genuine pushforward. -/
theorem measurable_characterChangeConj (a : Fˣ) (n : ℕ)
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)] :
    Measurable (characterChangeConj a n) :=
  (continuous_characterChangeConj a n).measurable

end Helpers

/-- For every p-adic field with its supplied topological data, every rank `n + 1`
and every unit `a`, conjugation `u ↦ d_a u d_a⁻¹` pushes the integral-normalized
unipotent Haar measure forward to `|a|^(-E)` times itself, where
`E = characterChangeRootExponent n` and `|·|` is the normalized absolute value. -/
def UnipotentCharacterChangeModulusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (a : F.Carrierˣ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    Measure.map (characterChangeConj a n) (unipotentHaar F.Carrier n) =
      ((characterChangeModulus (normalizedAbsoluteValue T) a n : ENNReal)⁻¹) •
        unipotentHaar F.Carrier n

end Langlands.RankinSelberg
