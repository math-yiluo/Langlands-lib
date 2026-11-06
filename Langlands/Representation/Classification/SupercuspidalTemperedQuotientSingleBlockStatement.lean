import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.Supercuspidal

/-!
# Tempered Langlands data of supercuspidal quotients have one block

An irreducible supercuspidal representation of `GL_(n+1)(F)` that is an
irreducible quotient of the standard module of a tempered Langlands datum
forces that datum to have exactly one block.
-/

namespace Langlands.Classification

universe uF uV

/-- If an irreducible supercuspidal representation of `GL_(n+1)(F)` is an
irreducible quotient of the standard module of a tempered Langlands datum, then
the datum's block shape has exactly one block. -/
def SupercuspidalTemperedQuotientSingleBlockStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (d : T.TemperedLanglandsDatum.{uV, uF} (n + 1))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    d.IsLanglandsQuotient π →
    (letI := T.topology; GeneralLinear.IsSupercuspidal π.representation) →
    d.shape.length = 1

end Langlands.Classification
