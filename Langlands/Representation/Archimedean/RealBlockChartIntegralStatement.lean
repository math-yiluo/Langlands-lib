import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integrability of the block chart bound for `P_{a,k}` of `GL_{a+k}(ℝ)`

For `X ∈ M_{k×a}(ℝ)` (the opposite unipotent radical `n̄(X) = [[1, 0], [X, 1]]` of the maximal
parabolic subgroup `P_{a,k}`), the Gram determinants of the lower rows of `n̄(X)` are
`D_l(X) = det(1 + X_{≤l}ᵀ X_{≤l})` (columns `0, …, l`) and `E_j(X) = det(1 + X^{(j)} X^{(j)ᵀ})`
(rows `j, …, k-1`). The statement `RealBlockChartIntegrableStatement` says that
`∏_l D_l(X)^{ε_l} · ∏_{j ≥ 1} E_j(X)^{-1/2}` is integrable on `M_{k×a}(ℝ)` when every tail sum
of `ε_l + 1/2` is negative. The statement is only stated here.
-/

noncomputable section

open MeasureTheory

namespace Langlands.Archimedean

set_option autoImplicit false

namespace RealBlockChart

variable {a k : ℕ}

/-- The columns `0, …, l` of `X`. -/
def colsUpTo (X : Matrix (Fin k) (Fin a) ℝ) (l : Fin a) : Matrix (Fin k) (Fin ((l : ℕ) + 1)) ℝ :=
  X.submatrix id (Fin.castLE (by omega))

/-- The rows `j, …, k-1` of `X`. -/
def rowsFrom (X : Matrix (Fin k) (Fin a) ℝ) (j : Fin k) : Matrix (Fin (k - j)) (Fin a) ℝ :=
  X.submatrix (fun i => ⟨(j : ℕ) + i, by omega⟩) id

/-- `D_l(X) = det(1 + X_{≤l}ᵀ X_{≤l})`. -/
def colGram (X : Matrix (Fin k) (Fin a) ℝ) (l : Fin a) : ℝ :=
  (1 + (colsUpTo X l).transpose * colsUpTo X l).det

/-- `E_j(X) = det(1 + X^{(j)} X^{(j)ᵀ})`. -/
def rowGram (X : Matrix (Fin k) (Fin a) ℝ) (j : Fin k) : ℝ :=
  (1 + rowsFrom X j * (rowsFrom X j).transpose).det

/-- The block chart bound `∏_l D_l(X)^{ε_l} · ∏_{j ≥ 1} E_j(X)^{-1/2}`. -/
def blockChartBound (ε : Fin a → ℝ) (X : Matrix (Fin k) (Fin a) ℝ) : ℝ :=
  (∏ l : Fin a, colGram X l ^ ε l) *
    ∏ j : Fin k, if (j : ℕ) = 0 then 1 else rowGram X j ^ (-(1 / 2 : ℝ))

end RealBlockChart

/-- **Statement (integrability of the real block chart bound).** Let `a, k ∈ ℕ` and
`ε_0, …, ε_{a-1}` be real numbers with `∑_{l ≥ j} (ε_l + 1/2) < 0` for every `j < a`. Then the
function `X ↦ ∏_{l<a} det(1 + X_{≤l}ᵀ X_{≤l})^{ε_l} · ∏_{1 ≤ j < k} det(1 + X^{(j)} X^{(j)ᵀ})^{-1/2}`
is integrable on `M_{k×a}(ℝ) = (Fin k → Fin a → ℝ)` with Lebesgue measure, where `X_{≤l}` is
formed by the columns `0, …, l` of `X` and `X^{(j)}` by its rows `j, …, k-1`. -/
def RealBlockChartIntegrableStatement : Prop :=
  ∀ (a k : ℕ) (ε : Fin a → ℝ),
    (∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l + 1 / 2 else 0) < 0) →
      Integrable fun X : Fin k → Fin a → ℝ =>
        RealBlockChart.blockChartBound ε (Matrix.of X)

end Langlands.Archimedean
