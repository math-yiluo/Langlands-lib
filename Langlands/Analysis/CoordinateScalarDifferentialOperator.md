# Coordinate scalar differential data and real-covector symbols

## The data

`Langlands.Analysis.CoordinateScalarOperator E d r` records finite-order
scalar differential data on a real normed vector space `E : Type v`, for
any `d r : ℕ`. `E` keeps its own `NormedAddCommGroup` and `NormedSpace ℝ`
structures. The structure has two fields:

- `basis : Module.Basis (Fin d) ℝ E`, a real basis made of actual vectors
  `b₀, …, b_{d-1}` of `E`. It does not introduce a coordinate norm or
  topology.
- `coefficient k w x : ℂ`, for each derivative order `k : Fin (r + 1)`
  (so `0 ≤ k ≤ r`), each ordered word `w : Fin k → Fin d` of basis
  directions of length `k`, and each point `x : E`.

The fields contain no regularity, ellipticity, symbol or
analytic-solution assumption.

## The action

For `F : E → ℂ` and `x : E`, `D.action F x` is

  `∑_{k=0}^{r} ∑_{w : Fin k → Fin d} coefficient k w x · (D^k F)(x)(b_{w 0}, …, b_{w (k-1)})`,

where `D^k F (x) = iteratedFDeriv ℝ k F x` is Mathlib's real `k`-th
iterated Fréchet derivative, a continuous `k`-multilinear map evaluated
here on the word of basis vectors. The zero-order term (`k = 0`, the
unique empty word) is `coefficient 0 ∅ x · F x`. Each order up to `r` is
present. `action` is an unbundled function of `F`. Mathlib's iterated
derivative is defined for every function, using the value zero of
`fderiv` at points of non-differentiability. So no linearity on
arbitrary nonsmooth functions is claimed and no algebra homomorphism is
defined. Uses of the
action for differential equations need their own smoothness hypotheses.

Several ordered words can give the same mixed partial derivative on a
smooth function: for `C^k` functions the iterated derivative is
symmetric. So the coefficient array of an operator is not unique. The
file defines no quotient, normal form or composition calculus.

## The highest-order symbol

For a point `x` and a real continuous covector `ξ : E →L[ℝ] ℝ`,

  `D.principalSymbol x ξ = ∑_{w : Fin r → Fin d} coefficient r w x · ∏_{j} (ξ(b_{w j}) : ℂ)`.

It keeps only the order-`r` coefficients (index `Fin.last r`). Each
derivative direction `b_{w j}` is replaced by the real number `ξ(b_{w j})`,
and the real product is embedded into `ℂ`. **No factor of `i` is
included.** This is the source's convention in (1.5), where `∂/∂x^α` is
replaced by the real `ξ_α`. A Fourier-transform argument must insert
the factor `i^r` itself, as the source does in (5.8) with `L'(iξ)`.

## The predicates

All three are `Prop`-valued definitions that unfold to explicit
properties of the given coefficients and of `principalSymbol`.

- `AnalyticCoefficientsOn D S`: for every `k` and every word `w`, the
  function `coefficient k w : E → ℂ` is real analytic at each point of
  `S` (`AnalyticOnNhd ℝ`, i.e. it has a convergent real power series
  expansion on a neighbourhood of each point of `S`).
- `IsEllipticOn D S`: `principalSymbol x ξ ≠ 0` for every `x ∈ S` and
  every nonzero `ξ : E →L[ℝ] ℝ`.
- `IsUniformlyEllipticOn D S`: there is one real `c > 0` such that
  `c · ‖ξ‖^r ≤ ‖principalSymbol x ξ‖` for all `x ∈ S` and all
  `ξ : E →L[ℝ] ℝ`. Here `‖ξ‖` is the operator norm of `ξ` for the
  original norm of `E`, and `‖·‖` on the right is the complex absolute
  value.

## Proved facts

- `principalSymbol_smul`: `principalSymbol x (c • ξ) = c^r · principalSymbol x ξ`
  for real `c`. Each of the `r` factors gives one factor of `c`.
- `IsUniformlyEllipticOn.isEllipticOn`: the uniform bound implies
  ellipticity on the same set, because `c · ‖ξ‖^r > 0` when `ξ ≠ 0`.
- `AnalyticCoefficientsOn.mono`, `IsEllipticOn.mono`,
  `IsUniformlyEllipticOn.mono`: each predicate passes to subsets (the
  uniform bound with the same constant).

No converse, and no analytic-regularity statement, is proved.

## Degenerate cases

`r = 0` and `d = 0` give well-defined data. For `r = 0` the action is
`coefficient 0 ∅ x · F x`. The symbol is the zero-order coefficient,
since the empty product is `1`. For `d = 0` the basis is empty, so `E`
is the zero space. Every covector is then zero, so `IsEllipticOn` holds
trivially. No positive-dimension hypothesis is imposed.

## Relation to the source

This is an internal coordinate realization of the scalar case (`N = 1`)
of the general linear systems in C. B. Morrey and L. Nirenberg, *On the
analyticity of the solutions of linear elliptic systems of partial
differential equations*, Comm. Pure Appl. Math. 10 (1957), 271–290. It
is not a verbatim transcription. The registered complete source is
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`
(SHA-256 `61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`).
The source passages it follows are:

- Section 1, equations (1.4)–(1.5), printed page 273 / PDF page 3. The
  operators are polynomials `L(x, ∇)` in `∇ = (∂/∂x¹, …, ∂/∂x^ν)` with
  complex coefficients depending on `x`. `L'` is the part of top order.
  Ellipticity (1.5) means `L'(x, ξ) ≠ 0` for real `ξ ≠ 0`; for
  `N = 1` the determinant is `L'` itself, of order `Q = s + t`, here
  `r`.
- Section 2, printed pages 275–276 / PDF pages 5–6. Here arrays
  ("tensors") are indexed by ordered lists of coordinate indices, and
  `∇^p` is the array of all ordered `p`-th partial derivatives. The word
  index `w` here plays the role of these ordered index lists.
- Section 5, printed pages 287–290 / PDF pages 17–20. It treats interior
  analytic regularity for analytic coefficients under uniform ellipticity
  (5.2), `|det L'(x, ξ)| ≥ k₀ |ξ|^Q` with `k₀ > 0` for real `ξ`, and
  passes to Fourier transforms using `L'(iξ)` in (5.8).

Differences from the source:

- The source uses Euclidean coordinates on a domain in `ℝ^ν`. Here the
  domain is an arbitrary real normed space with a chosen finite basis.
  When `E = ℝ^ν` with the standard basis, `iteratedFDeriv ℝ k F x`
  evaluated on standard basis vectors gives the ordered partial
  derivatives of a smooth `F`. In general, real covectors correspond to
  the coordinate vectors `(ξ(b₀), …, ξ(b_{d-1}))`.
- The source writes terms as monomials in `∇`. Here coefficients are
  indexed by ordered words, possibly with repeated letters. A
  multi-index term `a_α ∂^α` corresponds to one word whose letter counts
  are `α`. Conversely, on smooth functions the word-indexed sum equals
  the multi-index operator whose `α`-coefficient is the sum over words
  with letter counts `α`.
- (5.2) uses the Euclidean norm `|ξ|`. `IsUniformlyEllipticOn` uses the
  dual operator norm of the given norm of `E`.
- Section 1 assumes `Q > 0`, calling systems with `Q = 0` trivial. Here
  order `r = 0` is allowed as data.

None of these comparisons is proved here. A later proof using the source
must establish them, including the norm-equivalence constants relating
`‖ξ‖` to the Euclidean norm of the coordinate vector of `ξ`.

## Scope

The file constructs data and predicates and proves the elementary facts
listed above. Fourier L² estimates, cutoff estimates, factorial
derivative bounds, Sobolev estimates, analytic elliptic regularity and
the specialization to archimedean Cartan polynomials are separate
obligations.

Worker 94 wrote the first draft. Worker 881 revised it and added the
implication and restriction lemmas.
