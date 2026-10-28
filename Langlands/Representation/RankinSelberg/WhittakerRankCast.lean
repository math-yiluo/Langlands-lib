import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Group.GL.RankReindex

/-! # Equality transport of Whittaker functions -/

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear Whittaker HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F) {m n : ℕ}

/-- Transport along an equality of ranks retains the actual coefficient
function, evaluated after the corresponding numerical matrix reindexing. -/
def whittakerRankCast (h : m = n) (W : WhittakerFunctions ψ m) :
    WhittakerFunctions ψ n :=
  h ▸ W

theorem whittakerRankCast_apply (h : m = n) (W : WhittakerFunctions ψ m)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (whittakerRankCast ψ h W).val g =
      W.val (reindex (finCongr (congrArg (· + 1) h.symm)) g) := by
  subst n
  have hg : reindex (finCongr (rfl : m + 1 = m + 1)) g = g := by
    apply Units.ext
    rfl
  simp only [whittakerRankCast, hg]

end Langlands.RankinSelberg.InducedTailIntermediate
