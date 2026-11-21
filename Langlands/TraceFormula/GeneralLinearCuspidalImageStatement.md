# Cuspidal image for convolution on adelic `GL_n`

The module defines the proposition `Langlands.TraceFormula.GeneralLinearCuspidalImageStatement.{u}`.

## Library notation

- `AdelicGL K n` is `GL_n(𝔸_K)`. `RationalGL K n` is `GL_n(K)`, and
  `AdelicGL.rational K n` is the rational diagonal embedding.
- For a finite place `v : FinitePlace K`, `FiniteCompletion K v` is `K_v`. The map `ι_v` first
  applies `FiniteAdelicGL.localInclusion K n v`, inserting the local matrix at `v` and the
  identity at the other finite places. It then applies `AdelicGL.ofFinite K n`, inserting
  the identity at the infinite places.
- For `h : a + b = n`, `blockUnipotent h Z` is the matrix `[[1, Z], [0, 1]]` with the first
  `a` coordinates in the first block. As the `a × b` matrix `Z` varies, these matrices
  give the unipotent radical of the standard upper block parabolic of type `(a, b)`.
- `ContinuousRationalFunctions K n` consists of continuous complex-valued functions on
  `GL_n(𝔸_K)` invariant under left translation by `GL_n(K)`.
  `ContinuousRationalFunctions.evaluate K n F x` evaluates the underlying function at `x`.
- `IsCuspidal K n F` means that for each `a + b = n` with `a, b > 0` and each `g`, the
  constant term of `F` at `g` vanishes. The Library integrates `F(u g)` over
  `N(K) \ N(𝔸_K)` for the corresponding block unipotent radical `N`, using the normalized
  Haar probability `matrixQuotientHaar K a b` on `a × b` matrices over `𝔸_K / K`.

## Statement

Let `K : Type u` be a number field with the instance `[CompactSpace (AdeleQuotient K)]`.
Let `n : ℕ`, give `GL_n(𝔸_K)` its Borel σ-algebra, and let `μ` be a left Haar measure
on it. Fix a finite place `v` of `K` and a continuous, compactly supported
`f : GL_n(𝔸_K) → ℂ`.

For every `a, b : ℕ` with `h : a + b = n`, `a > 0` and `b > 0`, every additive Haar
measure `ν` on `a × b` matrices over `K_v` with the Borel σ-algebra, and every
`x, y ∈ GL_n(𝔸_K)`, assume

`∫ f(x · ι_v(blockUnipotent h Z) · y) dν(Z) = 0`.

For every `φ : GL_n(𝔸_K) → ℂ` with `φ(γ x) = φ(x)` for all `γ ∈ GL_n(K)` and
`x ∈ GL_n(𝔸_K)`, and with `LocallyIntegrable φ μ`, there exists
`F : ContinuousRationalFunctions K n` satisfying `IsCuspidal K n F` and

`ContinuousRationalFunctions.evaluate K n F x = ∫ f(g) φ(x g) dμ(g)`

for all `x ∈ GL_n(𝔸_K)`. Thus the right convolution `R(f)φ` is continuous, left
`GL_n(K)`-invariant and cuspidal. For `n ≤ 1` there is no split into two positive
blocks, so the vanishing hypothesis on `f` and the cuspidality condition are vacuous.

## Source

Getz and Hahn's *An Introduction to Automorphic Representations* (2024),
Definition 16.4.1 and Lemma 16.4.2 with its proof, appear on printed p. 430
(PDF p. 438 of the registered source `getz-hahn-2024-automorphic-representations`).
The lemma uses a smooth, compactly supported test function `f = f_v ⊗ f^v` on
`A_G \ G(𝔸_K)` with `f_v` supercuspidal. Definition 16.4.1 requires the integral of
`f_v(g u h)` along the radical of every proper local parabolic to vanish for every
`g` and `h`. The proof takes `φ ∈ L²([G])` and uses the local vanishing to kill the
adelic unipotent integral after unfolding a constant term.
[Getz–Hahn, Chapter 16](https://link.springer.com/chapter/10.1007/978-3-031-41153-3)

The Lean proposition is derived from that lemma for `GL_n`. The displayed vanishing on
two-sided translates of the local radicals of the standard maximal block parabolics
takes the place of a factorization with a supercuspidal factor. In a product test, the
`v`-component of `x · ι_v(u) · y` is `x_v u y_v`, and the other components are independent
of `u`. The proposition takes `f` and the convolution measure on the full `GL_n(𝔸_K)`.
The input `φ` is pointwise left `GL_n(K)`-invariant and locally integrable. The output
is expressed through `ContinuousRationalFunctions` and the Library's `IsCuspidal`.
