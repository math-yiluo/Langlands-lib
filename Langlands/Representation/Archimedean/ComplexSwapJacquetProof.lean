import Langlands.Representation.Archimedean.ComplexSwapJacquetFunctional
import Langlands.Representation.Archimedean.ComplexSwapJacquetLie
import Langlands.Representation.Archimedean.ComplexPermutationSwap

/-!
# Rank-one Jacquet functionals for an adjacent swap

This file proves `ComplexPermutation.SwapJacquetStatement`: for `ds = pre ++ d :: e :: post`
with `Re(t_d - t_e) ≥ 0` and `(l_d, t_d) ≠ (l_e, t_e)`, the `U(n)`-finite vectors of the
standard module of `ds` carry a nonzero Jacquet functional whose exponents are those of
`es = pre ++ e :: d :: post`.

The functional is `Λ_c(v) = ∫_ℂ (R(c E_jj) v - κ_j(c) v)(s x(z)) dz` at the positions
`i = |pre|` and `j = i + 1` (`ComplexSwapJacquet.functional`). The chart formulas
(`chartLieFacts`) come from `ComplexSwapJacquetLie`, the decay bounds from
`ComplexSwapJacquetDecay`, and the Jacquet property and the specialization from
`ComplexSwapJacquetFunctional`. The remaining input is a pair `(c, f)` with
`Λ_c(f) ≠ 0` (`swapJacquet_of_nonvanishing`).
-/

noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-- The pointwise chart formulas of `ComplexSwapJacquetLie`, packaged for
`ComplexSwapJacquetFunctional`. -/
theorem chartLieFacts (ds : List ComplexCharacterData) (hn : ds.length = n) (i j : Fin n)
    (hj : (j : ℕ) = i + 1) : ChartLieFacts ds hn i j hj where
  single_ij _ hf w z := rightDerivative_chart_single_ij hj hf.1 w z
  strictUpper _ hf X hX hXij z := rightDerivative_chart_strictUpper hj hf X hX hXij z
  diag_other _ hf k hki hkj c z := rightDerivative_chart_diag_other hn hj hf k hki hkj c z
  diag_j _ hf c z := rightDerivative_chart_diag_j hn hj hf c z
  diag_i _ hf c z := rightDerivative_chart_diag_i hn hj hf c z
  one_strictUpper _ hf X hX := rightDerivative_one_strictUpper hf X hX
  one_diag _ hf k c := rightDerivative_one_diag hn hf k c

/-- `SwapJacquetStatement`, given a nonvanishing integral of the integrand at the positions of
`d` and `e`. -/
theorem swapJacquet_of_nonvanishing
    (hnz : ∀ (pre post : List ComplexCharacterData) (d e : ComplexCharacterData) (n : ℕ)
      (hn : (pre ++ d :: e :: post).length = n) (i j : Fin n) (_hi : (i : ℕ) = pre.length)
      (hj : (j : ℕ) = i + 1), 0 ≤ (d.exponent - e.exponent).re →
      (d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent) →
      ∃ (c : ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ), f ∈ KFs n (pre ++ d :: e :: post) ∧
        ∫ z, integrand (pre ++ d :: e :: post) hn i j hj c f z ≠ 0) :
    ComplexPermutation.SwapJacquetStatement := by
  intro pre post d e n hn hre hne
  have hlt : pre.length + 1 < n := by
    rw [← hn]
    simp
  let i : Fin n := ⟨pre.length, by omega⟩
  let j : Fin n := ⟨pre.length + 1, hlt⟩
  have hi : (i : ℕ) = pre.length := rfl
  have hj : (j : ℕ) = i + 1 := rfl
  exact exists_swapJacquetFunctional pre post d e hn
    ((ComplexPermutation.length_swap pre post d e).trans hn) i j hi hj hre
    (chartLieFacts _ hn i j hj) (hnz pre post d e n hn i j hi hj hre hne)

end Langlands.Archimedean.ComplexSwapJacquet
