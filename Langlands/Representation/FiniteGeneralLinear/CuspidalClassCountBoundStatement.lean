import Langlands.FieldTheory.IrreduciblePolynomialLabels
import Langlands.Representation.FiniteGeneralLinear.Cuspidal
import Mathlib.SetTheory.Cardinal.Finite

/-!
# At most `|𝔍(n, k)|` cuspidal classes of `GL_n(k)`

The upper-bound half of the Green parametrisation cited in Bushnell–Kutzko 1994 after (3.6).
-/

namespace Langlands.FiniteGeneralLinear

open Langlands.FieldTheory

/-- For every finite field `k` (in any universe `u`) and every `n ≥ 1`, the general linear
group `GL_n(k)` has at most `|𝔍(n, k)|` isomorphism classes of irreducible cuspidal complex
representations on carriers in `Type w`. -/
def CuspidalClassCountBoundStatement.{u, w} : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (n : ℕ), 0 < n →
    ENat.card (CuspidalClass.{u, w} n k) ≤ (irreduciblePolynomialLabels n k).encard

end Langlands.FiniteGeneralLinear
