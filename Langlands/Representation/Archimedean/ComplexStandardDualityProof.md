# Duality of complex principal series with inverse characters

Module: `Langlands.Representation.Archimedean.ComplexStandardDualityProof`.

## Result

`Langlands.Archimedean.complexStandardDuality : ComplexStandardDualityStatement`.

Let `n` be a natural number. Let `ds, ds'` be lists of complex character data whose position
characters are pointwise inverse: `complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1`.
The theorem gives a bilinear pairing `Q` of the `U(n)`-finite functions of `complexStandardModule n ds`
and `complexStandardModule n ds'` with three properties. It is invariant under right translation
by `U(n)`. It satisfies `Q(R(X) f, h) + Q(f, R(X) h) = 0` for the right derivatives
`R(X) = rightDerivative (matrixModel ℂ n) X`, `X ∈ M_n(ℂ)`. And it is nondegenerate in the
second argument.

The pairing is the standard one, `Q(f, h) = ∫_{U(n)} f(k) h(k) dk`, for the Haar probability
measure on `U(n)` (`ComplexDuality.integralPairing`).

## Proof

The theorem applies `ComplexDuality.complexStandardDuality_of_lieInvariance`
(module `ComplexDuality.Pairing`) to the `𝔤`-invariance lemma
`ComplexDuality.integral_rightDerivative_mul_add_eq_zero` (module `ComplexDuality.LieInvariance`),
specialized to the measure `unitaryHaar n`. The pieces are as follows.

- **Measure** (`ComplexDuality.UnitaryHaar`). `unitaryHaar n` is the Haar probability measure of
  the compact group `U(n) = unitaryCompact ℂ n`. On a compact group it is both left and right
  invariant. Continuous functions are integrable for it, and a nonzero continuous nonnegative
  function has positive integral.
- **Bilinearity and `U(n)`-invariance** (`ComplexDuality.Pairing`). Principal-series functions
  are continuous, so the integrals exist, which gives bilinearity. Invariance under
  `R(k)`, `k ∈ U(n)`, is right invariance of `unitaryHaar n`.
- **Nondegeneracy** (`ComplexDuality.GramWeight`). For `h ≠ 0` the partner
  `f = ψ · conj h` lies in the `U(n)`-finite principal series of `ds`. Here `ψ` is a product of
  real powers of ratios of Gram determinants of the lower rows of `g`. It is smooth, right
  `U(n)`-invariant and equal to `1` on `U(n)`, and it transforms under the upper triangular Borel
  subgroup by `∏ |χᵢ(aᵢ)|²`. On `U(n)` the integrand `f h` is `|h|²`. By the Iwasawa
  decomposition, `h` does not vanish identically on `U(n)`, so `Q(f, h) > 0`.
- **`𝔤`-invariance** (`ComplexDuality.LieInvariance`). Let `Φ` be
  the product of the extensions of `f` and `h` to all matrices. It is smooth on the invertible
  matrices, invariant on the left under the upper unipotent group, and it transforms on the left
  under the diagonal torus by `∏ᵢ |aᵢ|^{2(n-1-2i)}` (the modulus character of the Borel
  subgroup), because the characters are pointwise inverse. By the product rule,
  `R(X) f · h + f · R(X) h` at `k ∈ U(n)` is `DΦ(k)(k X)`. Put `Z = k X kᴴ`, so `k X = Z k`, and
  expand `Z = Σ Z_ab E_ab`. Terms with `a < b` vanish by unipotent invariance. Terms with
  `a = b` give `2 Re Z_aa (n - 1 - 2a) Φ(k)` by the torus transformation. For `b < a`,
  `Z_ab E_ab` is a real combination of the skew-Hermitian matrices `E_ab - E_ba` and
  `i(E_ab + E_ba)` plus a strictly upper triangular term. The product rule, with the coefficients
  `Re Z_ab` and `Im Z_ab` viewed as functions of `k`, turns each such term into a pair term
  (derivatives of `Re Z_ab · Φ` and `Im Z_ab · Φ` along skew-Hermitian directions) minus
  `2 (Re Z_bb - Re Z_aa) Φ(k)`. A counting identity cancels all multiples of `Φ(k)`, so
  `DΦ(k)(k X)` is a sum of pair terms. Each pair term integrates to zero: for skew-Hermitian `Y`,
  `t ↦ ∫ Ψ(exp(t Y) k) dk` is constant by left invariance of the measure, and differentiating
  under the integral at `t = 0` gives `∫ DΨ(k)(Y k) dk = 0`. The lemma is stated for any left
  invariant finite measure on `U(n)`; here it is applied to `unitaryHaar n`.

The proof follows the standard argument for the invariant pairing between principal series
induced from inverse characters (the integration formula `∫_G = ∫_B ∫_K` is replaced by the
infinitesimal computation above). The Gram-determinant construction of the partner function
is an auxiliary device of this formalization.
