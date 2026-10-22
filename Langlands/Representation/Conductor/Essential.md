# Jacquet's corrected essential vector on `GL_(n+2)`

This module states the defining property of the essential vector of
Jacquet (2012), Theorem 1 (p. 517), together with the uniqueness clause after
that theorem. It defines the property and selects the vector only from a proof
of unique existence. It does not prove existence or uniqueness. The
coefficient field is the complex numbers.

The representation `π` acts on `GL_((n+1)+1)(F)`, so Jacquet's rank `r` is
`n + 2 ≥ 2`. The integrals run over the quotient for `GL_(n+1)`, which is
Jacquet's `G_(r-1)`. The Satake parameters are tuples `x : Fin (n + 1) → ℂˣ`,
which are Jacquet's `(r-1)`-tuples of nonzero complex numbers.

## Additive characters of conductor `O`

`F` is a field with the supplied valuation `v = ValuativeRel.valuation F` and
topology, and `O = v.integer`. For a unitary additive character `ψ`,
`HasIntegerConductor ψ` says two things:

* `ψ` is trivial on `O`;
* every `x ∈ F` with `ψ(x y) = 1` for all `y ∈ O` lies in `O`.

Together these say that `O` is the largest `O`-submodule of the form `x O` on
which `ψ` is trivial. This is Jacquet's hypothesis (p. 515) that the conductor
of `ψ` is the ring of integers. The Library also has Tate's integer conductor
`Langlands.PadicField.TopologicalData.additiveConductor` for its packaged
p-adic fields. Conductor `O` corresponds to the value `0` there, but the module
does not prove that correspondence.

## The spherical Whittaker function for `ψ̄`

`inverseSphericalWhittaker hψ hϖ q x` is the published explicit spherical
Whittaker function `sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q x`
of `Langlands.Representation.Whittaker.Spherical`. Its character is the
published inverse standard character `u ↦ ψ(Σ_i u_(i,i+1))^(-1)` of the upper
unitriangular group of `GL_(n+1)(F)`. The inputs are:

* `hψ`: `ψ` is trivial on `O`;
* `hϖ : IsUniformizingElement v ϖ` from the published Iwasawa module;
* an explicit natural number `q`;
* the parameters `x`.

The function is packaged as an element of Worker 31's published
`InverseWhittakerFunctions ψ n`, the type of the second argument of the
corank-one JPSS integral. The membership proof is the published
`sphericalWhittaker_mem` together with the integral triviality of the inverse
standard character.

The module proves three facts:

* `inverseSphericalWhittaker_apply` evaluates the function to the published
  explicit function.
* `inverseSphericalWhittaker_one` gives the value `1` at the identity.
* `inverseSphericalWhittaker_mul_integral` gives right invariance under the
  published integral subgroup `integralSubgroup O n`, the image of
  `GL_(n+1)(O)`.

Jacquet (p. 516) defines `W(g; x; ψ)` instead by four properties: right
`G_r(O)`-invariance, `θ_(r,ψ)`-equivariance, the Hecke eigen-equation with
Satake eigenvalue at `x`, and `W(e) = 1`. The module does **not** prove that
the explicit function has these properties or that it equals Jacquet's
function, so the identification with Shintani's formula is a separate
obligation. The explicit formula and its sources are documented in
`Langlands/Representation/Whittaker/Spherical.md`.

## The right-hand side

For a polynomial `P` and a tuple `x : Fin m → ℂˣ`, `essentialFactor P x` is
the rational function

`∏_i P(x_i X)^(-1)`

in `RationalFunctions = RatFunc ℂ`, where `P(x_i X)` is `P.comp (C x_i * X)`.
At `X = q^(-s)` this is Jacquet's `∏_(1 ≤ i ≤ r-1) P(q^(-s) x_i)^(-1)`.
`essentialFactor_eq` rewrites it as the inverse of the single polynomial
`∏_i P(x_i X)`.

## The identity of Theorem 1

`SatisfiesEssentialIdentity q ψ abv μ hψ hϖ P W` has the following inputs:

* the explicit `q`, `ψ` and absolute value `abv : AbsoluteValue F ℝ`;
* an explicit measurable structure on the published quotient
  `LeftUnipotentQuotient n F = N_(n+1) \ GL_(n+1)(F)`, with a measure `μ` on it;
* a polynomial `P`;
* `W : WhittakerFunctions ψ (n + 1)`, a `ψ`-Whittaker function on
  `GL_((n+1)+1)(F)`.

For every `x : Fin (n + 1) → ℂˣ`, the property requires the following, where
`W'_x` is `inverseSphericalWhittaker hψ hϖ q x`:

1. There is a real `a` such that, for every complex `s` with `Re s > a`, the
   published `CorankOneConverges ψ abv μ W W'_x s` holds. That is, the
   descended integrand

   `g ↦ W(diag(g, 1)) W'_x(g) |det g|^(s - 1/2)`

   is integrable for `μ`. Here `|det g|^s` is the published
   `determinantWeight abv g s`.
2. The published `HasRationalContinuation q (corankOneIntegral ψ abv μ W W'_x)
   (essentialFactor P x)` holds. On some right half-plane `Re s > a'`, the
   denominator of the rational function does not vanish at `q^(-s)`, and the
   integral

   `∫_(N_(n+1) \ GL_(n+1)) W(diag(g, 1)) W'_x(g) |det g|^(s - 1/2) dμ(g)`

   equals the rational function evaluated at `q^(-s)`.

The thresholds `a` and `a'` may depend on `x`. Jacquet's Theorem 1 writes the
identity as an equality of functions of `s`. The module reads it as convergence
on a right half-plane together with agreement there with the stated rational
function in `q^(-s)`. This is the same convention as Worker 31's published zeta
values.

## Jacquet's normalizations

In this section `F` is also an `IsNonarchimedeanLocalField`, and the following
measurable structures are explicit instance arguments:

* on `GL_(n+1)(F)` and its upper unitriangular subgroup, both Borel;
* on `GL_1(F)`, Borel;
* on the two quotients `LeftUnipotentQuotient n F` and
  `LeftUnipotentQuotient 0 F`, whose Borel property is a field of the
  normalization.

The structure `IsJacquetNormalization q ψ abv ϖ μ` collects the normalizations
of Jacquet's pp. 515-516:

* `residueCardinality`: `q` is the cardinality `Nat.card` of the residue field
  of `O`;
* `uniformizer`: `ϖ` is a uniformizing element of `v`;
* `abv_uniformizer`: `abv ϖ = q⁻¹`;
* `abv_unit`: `abv x = 1` for every `x` with `v(x) = 1`;
* `conductor`: `HasIntegerConductor ψ`;
* `measure`: `μ` is compatible, in the sense of the published
  `QuotientIntegration.IsCompatible`, with the published Haar measures
  `generalLinearHaar F n` on `GL_(n+1)(F)` and `unipotentHaar F n` on
  `N_(n+1)(F)`. These give `GL_(n+1)(O)` and `N_(n+1)(O)` mass one.
* `borel`, `borel_rankOne`: the measurable structures on `N_(n+1) \ GL_(n+1)(F)`
  and on `N_1 \ GL_1(F)` are Borel. Without the second field, the published
  rank-one quotient measure used for the L-factor below could be a push-forward
  to an unrelated σ-algebra.

Jacquet's `|x| = q^(-v(x))` (p. 515) is recorded through the two conditions on
`abv`. Every nonzero `x` is a valuation unit times a power of `ϖ`, so those two
conditions determine `abv` on `F^×`; the module does not prove this. The module
also does not prove that a compatible `μ` exists. Jacquet's quotient measure is
the invariant quotient of the two normalized Haar measures (p. 516).

## The essential vector

Besides a normalization `h : IsJacquetNormalization q ψ abv ϖ μ`, the
essential-vector definitions take:

* a representation `π` of `GL_((n+1)+1)(F)` on a complex vector space `V`;
* a functional `ℓ ∈ glFunctionals ψ (n + 1) π`, equivariant for the standard
  character `u ↦ ψ(Σ_i u_(i,i+1))`;
* a vector `w` of the published coefficient model `coefficientModel π ℓ`, the
  space of functions `g ↦ ℓ(π(g) v)`.

`IsEssentialVector h π ℓ w` is the conjunction of two conditions.

1. **The identity.** There is a polynomial `P` with both of the following:
   * `IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`, so `P` is
     Worker 31's published normalized generator of the zeta values of `π × 1`.
     Here `1` is the trivial character of `GL_1(F)`, and `rankOneQuotientHaar F`
     is the published rank-one quotient measure. Thus
     `L(s, π × 1) = P(q^(-s))^(-1)`.
   * `SatisfiesEssentialIdentity q ψ abv μ h.conductor.1 h.uniformizer P w`.
2. **Restriction invariance.** The published `IsIntegralInvariantOnRestriction
   π ℓ w` holds, so that `w(diag(g k, 1)) = w(diag(g, 1))` for all
   `g ∈ GL_(n+1)(F)` and all `k` in the integral subgroup. This is Jacquet's
   extra uniqueness condition after Theorem 1. With it, the vector of
   Theorem 1 is called *the* essential vector.

`IsEssentialVector.satisfiesEssentialIdentity` proves that an essential vector
satisfies the identity for *every* `P` with
`IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P`. The proof uses
the published uniqueness of normalized generators,
`IsNormalizedGenerator.unique`.

`essentialVector h π ℓ hu` takes
`hu : ∃! w, IsEssentialVector h π ℓ w` and returns the witness of the
existence part. `essentialVector_spec` proves that this vector is essential,
and `isEssentialVector_iff_eq` proves that a vector is essential exactly when it
equals it. No vector is chosen without such a proof.

## What is not claimed

* **The L-factor.** Jacquet's `P` comes from the Godement–Jacquet factor
  `L(s, π)` (p. 517). Here `P` is the JPSS standard factor `L(s, π × 1)`,
  defined by the zeta integrals of `π` against the trivial character of
  `GL_1`. The module neither proves nor cites a proof that the two
  factors agree. That agreement is a separate obligation.
* **The spherical function.** The explicit spherical function is not proved to
  satisfy Jacquet's Hecke-eigen characterization.
* **The representation.** Irreducibility, admissibility, smoothness and
  genericity of `π` are not hypotheses, and `ℓ` may be any functional,
  including zero. For irreducible generic `π` and nonzero `ℓ`, the model
  `coefficientModel π ℓ` is Jacquet's `W(π; ψ)`, because the Whittaker
  functional is unique up to a scalar. The module does not prove this. If no
  standard L-polynomial exists, no vector is essential. This polynomial
  condition depends on `π`, not on the chosen `ℓ`: choosing `ℓ = 0` does
  not change the representation's standard L-polynomial.
* **Existence and uniqueness.** Neither existence nor uniqueness of an
  essential vector is asserted, so `essentialVector` requires
  unique existence as an explicit hypothesis.
* **The rank.** Rank `r = 1` is not covered. The rank is `n + 2 ≥ 2`, as in
  Section 1 of Jacquet's proof.

## Sources

* H. Jacquet, *A correction to Conducteur des représentations du groupe
  linéaire*, Pacific J. Math. 260 (2012), 515–525. The relevant pages are:
  * p. 515: `|x| = q^(-v(x))`, `ψ` of conductor `O_F`, the measure giving
    `G_r(O_F)` volume one, and `θ_(r,ψ)`;
  * p. 516: the measure giving `N_r(O_F)` measure one, the quotient measure,
    and the characterization of `W(g; x; ψ)`;
  * p. 517: Theorem 1, the uniqueness clause, and `L(s, π) = P(q^(-s))^(-1)`.
* H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  convolutions*, Amer. J. Math. 105 (1983), 367–464. This is the source of the
  JPSS L-factors that Worker 31's published module uses for `L(s, π × 1)`:
  §2.1, pp. 385–386 (conventions and `𝒲(π; ψ)`), and Theorem 2.7,
  pp. 390–391 (the normalized generator of the zeta values).
