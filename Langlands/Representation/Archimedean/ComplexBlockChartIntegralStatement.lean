import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integrability of the block chart bound for `P_{a,k}` of `GL_{a+k}(ℂ)`

For `X ∈ M_{k×a}(ℂ)` (the opposite unipotent radical `n̄(X) = [[1, 0], [X, 1]]` of the maximal
parabolic subgroup `P_{a,k}`), the Gram determinants of the lower rows of `n̄(X)` are
`D_l(X) = det(1 + X_{≤l}ᴴ X_{≤l})` (columns `0, …, l`) and `E_j(X) = det(1 + X^{(j)} X^{(j)ᴴ})`
(rows `j, …, k-1`). The statement `ComplexBlockChartIntegrableStatement` says that
`∏_l D_l(X)^{ε_l} · ∏_{j ≥ 1} E_j(X)^{-1}` is integrable on `M_{k×a}(ℂ)` when every tail sum of
`ε_l + 1` is negative. The statement is only stated here.
-/

noncomputable section

open MeasureTheory

open scoped Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ComplexBlockChart

variable {a k : ℕ}

/-- The columns `0, …, l` of `X`. -/
def colsUpTo (X : Matrix (Fin k) (Fin a) ℂ) (l : Fin a) : Matrix (Fin k) (Fin ((l : ℕ) + 1)) ℂ :=
  X.submatrix id (Fin.castLE (by omega))

/-- The rows `j, …, k-1` of `X`. -/
def rowsFrom (X : Matrix (Fin k) (Fin a) ℂ) (j : Fin k) : Matrix (Fin (k - j)) (Fin a) ℂ :=
  X.submatrix (fun i => ⟨(j : ℕ) + i, by omega⟩) id

/-- `D_l(X) = det(1 + X_{≤l}ᴴ X_{≤l})` (a positive real number; its real part). -/
def colGram (X : Matrix (Fin k) (Fin a) ℂ) (l : Fin a) : ℝ :=
  ((1 + (colsUpTo X l)ᴴ * colsUpTo X l).det).re

/-- `E_j(X) = det(1 + X^{(j)} X^{(j)ᴴ})` (a positive real number; its real part). -/
def rowGram (X : Matrix (Fin k) (Fin a) ℂ) (j : Fin k) : ℝ :=
  ((1 + rowsFrom X j * (rowsFrom X j)ᴴ).det).re

/-- The block chart bound `∏_l D_l(X)^{ε_l} · ∏_{j ≥ 1} E_j(X)^{-1}`. -/
def blockChartBound (ε : Fin a → ℝ) (X : Matrix (Fin k) (Fin a) ℂ) : ℝ :=
  (∏ l : Fin a, colGram X l ^ ε l) * ∏ j : Fin k, if (j : ℕ) = 0 then 1 else (rowGram X j)⁻¹

end ComplexBlockChart

/-- **Statement (integrability of the block chart bound).** Let `a, k ∈ ℕ` and `ε_0, …, ε_{a-1}`
be real numbers with `∑_{l ≥ j} (ε_l + 1) < 0` for every `j < a`. Then the function
`X ↦ ∏_{l<a} det(1 + X_{≤l}ᴴ X_{≤l})^{ε_l} · ∏_{1 ≤ j < k} det(1 + X^{(j)} X^{(j)ᴴ})^{-1}` is
integrable on `M_{k×a}(ℂ) = (Fin k → Fin a → ℂ)` with Lebesgue measure, where `X_{≤l}` is formed by
the columns `0, …, l` of `X` and `X^{(j)}` by its rows `j, …, k-1`. -/
def ComplexBlockChartIntegrableStatement : Prop :=
  ∀ (a k : ℕ) (ε : Fin a → ℝ),
    (∀ j : Fin a, ∑ l : Fin a, (if j ≤ l then ε l + 1 else 0) < 0) →
      Integrable fun X : Fin k → Fin a → ℂ =>
        ComplexBlockChart.blockChartBound ε (Matrix.of X)

end Langlands.Archimedean
