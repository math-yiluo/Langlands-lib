# Principal series of `GL_n(ℝ)` evaluated at the identity

Module: `Langlands.Representation.Archimedean.RealSubquotientEval` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is the first helper module for the proof of Harish-Chandra's subquotient theorem
`Langlands.Archimedean.RealPrincipalSeriesSubquotientStatement`; the overall argument is explained
in `RealPrincipalSeriesSubquotientProof.md`. The module collects facts about principal series of
`GL_n(ℝ)` near the identity, about derivatives of matrix representations of `O(n)`, and about
Frobenius reciprocity through evaluation at `1`. It is internal infrastructure; no definition here
is meant to match a definition of the literature beyond what its docstring says.

## Principal series

- `psList a e` (for `a : Fin n → ℂ`, `e : Fin n → Fin 2`) is the list of blocks
  `(List.ofFn (RealJacquetFrobenius.chars a e)).map RealBlock.character`. Its principal series
  is induced from the characters `x ↦ sgn(x)^{e_j} |x|^{a_j - (n-1)/2 + j}`, with zero-based
  positions `j = 0, …, n-1`. These are the Library's `RealJacquetFrobenius.chars a e`, whose
  exponents are `RealJacquetFrobenius.expo a j = a_j - (n-1)/2 + j`. The Library's
  `principalSeries` multiplies the `j`-th inducing character by the normalizing factor
  `|x|^{(n-1)/2 - j}` (`principalSeriesCharacter`). This factor cancels the shift, so on
  `diag(d)` a function in this principal series transforms by `∏ⱼ sgn(d_j)^{e_j} |d_j|^{a_j}`
  (Library `RealJacquetFrobenius.principalSeriesCharacter_eq`, with `diagChar a e`). The exponent
  `a_j` therefore appears in the derivative formula below.
- `PS a e` is the space of `O(n)`-finite functions of `realStandardModule n (psList a e)`, that
  is, `kFiniteFunctions (realStandardModule n (psList a e)) (unitaryCompact ℝ n)`.
- `rightDerivative_upper_apply_one`: for `f` in `principalSeries ℝ n (posChar a e)` and an upper
  triangular real matrix `U`, `(R(U) f)(1) = (∑ⱼ aⱼ Uⱼⱼ) f(1)`. The proof differentiates `f` along
  the curve `exp(t·diag U)(1 + t N)`, `N = U - diag U`, on which `f` equals
  `exp(t ∑ⱼ aⱼ Uⱼⱼ) f(1)`.

## Derivatives of matrix representations of `O(n)`

- `IsTypeDerivative τ D` (a `Prop`): `D : 𝔤𝔩_n(ℝ) →ₗ[ℝ] Mat_d(ℂ)` is the derivative of
  `τ : O(n) →* Mat_d(ℂ)`. For every curve `γ` in `O(n)` with `γ(0) = 1` whose entries have
  derivative `X` at `0`, the entries of `τ(γ(t))` have derivative `D(X)` at `0`.
- `apply_skew_intertwiner`: let `T` be a `K`-intertwiner from `τ` into a
  `(𝔤𝔩_n(ℝ), O(n))`-module (`T ∈ gkIntertwiners ρ d τ`, `IsRealGKModule n ρ π`) and let `Y` be
  antisymmetric. Then `π(1 ⊗ Y)(T x) = T(D(Y) x)`. The proof uses the curve `exp(tY)` in `O(n)`,
  the derivative clause of `IsRealGKModule`, and `hasDerivAt_apply_mulVec`.

## Sign functionals and Frobenius reciprocity

- `matRep τ` is `τ` viewed as a `Representation` on `ℂ^d`.
- `IsSignFunctional τ e φ`: for every sign matrix `s_j = signReflection n j`,
  `φ(τ(s_j) x) = (-1)^{e_j} φ(x)`.
- `exists_frobenius_intertwiner` (**Frobenius reciprocity**): for continuous `τ`, any `a`, and a
  sign functional `φ` with signs `e`, there is
  `T ∈ gkIntertwiners (realStandardRep n (psList a e)) d τ` with `(T x)(1) = φ(x)` for all `x`.
  It is built from the Library's Frobenius map `RealJacquetFrobenius.frobLin (matRep τ) φ a e`
  (smoothness, left equivariance, right `O(n)`-translation, `O(n)`-finiteness).
- `signReflection_mul_self`, `signReflection_comm`: the sign matrices are commuting involutions.
- `mem_span_signFunctional`: every linear functional on `ℂ^d` lies in the span of the sign
  functionals. The proof splits a functional `ψ` as `ψ = ½(ψ + ψ∘τ(s_j)) + ½(ψ - ψ∘τ(s_j))`, one
  sign matrix at a time, by induction over a finite set of indices.
- `eq_zero_of_signFunctional`: a vector killed by all sign functionals is `0`.
