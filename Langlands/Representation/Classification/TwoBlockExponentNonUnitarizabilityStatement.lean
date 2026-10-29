import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Unitary.Basic

/-!
# Non-unitarizability of `ν^s ρ × ν^(-s) ρ` for large negative `s`

For an irreducible unitarizable smooth representation `ρ` of `GL_k(F)` with
`k > 0` and a real `s < -k/2`, the actual upper normalized product
`ν^s ρ × ν^(-s) ρ` on `GL_{2k}(F)` admits no invariant positive definite
Hermitian form. Here `ν = |det|`. This is the unbounded matrix coefficient step
of Zelevinsky 1980, Proposition 1.11, printed p.175. This module supplies the
proposition only.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For positive rank `k`, an irreducible unitarizable smooth representation `ρ`
of `GL_k(F)` and a real `s < -k/2`, the actual upper normalized product
`ν^s ρ × ν^(-s) ρ` (first block twisted by `ν^s`, second by `ν^(-s)`) is not
unitarizable. This definition supplies the proposition only. -/
def TwoBlockLargeExponentNonUnitarizable : Prop :=
  letI := T.topology
  ∀ (k : ℕ) (hk : 0 < k)
    (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)),
    ρ.representation.IsIrreducible → IsUnitarizable ρ.representation →
    ∀ s : ℝ, s < -(k : ℝ) / 2 →
      ¬ IsUnitarizable (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk ρ ρ) ![s, -s]).representation

end Langlands.Classification
