import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

/-!
# The rank-one chart and the integrand of the swapped Jacquet functional

For adjacent positions `i` and `j = i + 1` of `GL_n(ℂ)`, `chart i j hj z = s x(z)` is the
permutation matrix `s` of the transposition `(i j)` times the upper unipotent matrix
`x(z) = 1 + z E_{ij}`: the identity matrix with the block `[[0, 1], [1, z]]` in rows and
columns `i, j`.

`kappa ds hn k c` is the derivative at `t = 0` of the character of the standard module of `ds`
along `exp(t c E_kk)`, namely `Re c · a_k + Im c · b_k` with `a_k = 2 t_k + (n - 1) - 2k` and
`b_k = i l_k` (`t_k` the exponent and `l_k` the weight of the `k`-th character of `ds`).

`integrand ds hn i j hj c f z` is `(R(c E_jj) f - kappa_j(c) f)(chart z)`, the function whose
integral over `z ∈ ℂ` is the rank-one Jacquet functional.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.LocalFactor.Archimedean

variable {n : ℕ}

theorem ne_of_val_eq_succ {i j : Fin n} (hj : (j : ℕ) = i + 1) : i ≠ j := by
  intro h
  rw [h] at hj
  omega

/-- The matrix `s x(z)`: the permutation matrix of the transposition `(i j)` times
`1 + z E_{ij}`. -/
def chart (i j : Fin n) (hj : (j : ℕ) = i + 1) (z : ℂ) : Langlands.GeneralLinear n ℂ :=
  Matrix.GeneralLinearGroup.swap ℂ i j *
    Matrix.GeneralLinearGroup.transvection i j (ne_of_val_eq_succ hj) z

/-- The derivative at `t = 0` of the character of the standard module of `ds` along
`exp(t c E_kk)`: `Re c · (2 t_k + (n - 1) - 2k) + Im c · i l_k`. -/
def kappa (ds : List ComplexCharacterData) (hn : ds.length = n) (k : Fin n) (c : ℂ) : ℂ :=
  (c.re : ℂ) * (2 * (ds.get (Fin.cast hn.symm k)).exponent + ((n : ℂ) - 1) -
      2 * ((k : ℕ) : ℂ)) +
    (c.im : ℂ) * (Complex.I * ((ds.get (Fin.cast hn.symm k)).weight : ℂ))

/-- The integrand `(R(c E_jj) f - kappa_j(c) f)(s x(z))` of the rank-one Jacquet functional. -/
def integrand (ds : List ComplexCharacterData) (hn : ds.length = n) (i j : Fin n)
    (hj : (j : ℕ) = i + 1) (c : ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) (z : ℂ) : ℂ :=
  rightDerivative (matrixModel ℂ n) (Matrix.single j j c) f (chart i j hj z) -
    kappa ds hn j c * f (chart i j hj z)

theorem chart_val (i j : Fin n) (hj : (j : ℕ) = i + 1) (z : ℂ) :
    ((chart i j hj z : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.swap ℂ i j * Matrix.transvection i j z :=
  rfl

end Langlands.Archimedean.ComplexSwapJacquet
