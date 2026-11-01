# Adjacent-rank finite integral products

This derived prerequisite proves the actual finite sum of integral products in
JPSS Section 6.3 (10), printed pages 435–436, at every supplied parameter where
the corank-one integral and all its equal-rank and matrix factors converge.
It combines the actual finite coefficient convolution with determinant-slice
spectral expansions and finite-interval Cauchy products.

The registered source is **jpss-1983-rankin-selberg**, Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983), SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Theorem 3.1, printed pages 404–405, and Section 6 through the case enumeration
in Section 7.1, printed pages 427–439, were read for the surrounding proof.
This module implements the passage from (9) to (10), pages 435–436.
The bounded registered-errata checks recorded in the worker's source reading
found no JPSS-specific erratum.

## Actual integral expression

Use a canonical p-adic field `F`, its normalized absolute value, every natural
`r`, a nontrivial unitary additive character `ψ`, and a supplied Borel measure
`ν` on the actual left-unipotent quotient of `GL_(r+1)`. Write
`z = spectralPoint q s`. The group rank `r+1` includes rank one.

`adjacentRankFiniteProductValue` is the literal expression

`∑ i, equalRankIntegral(W, B_i, φ, s) *
  matrixIntegral(Φ, s+r/2, χ(det h) f_i(h))`.

Here `W` is a Whittaker function, `B` is a finite family of inverse-character
Whittaker functions, `Φ` is a Schwartz–Bruhat test on the full square-matrix
space, `φ` is a Schwartz–Bruhat row test, `χ` is a quasicharacter, and the
`f_i` are complex-valued group functions. The matrix integral uses the existing
`generalLinearHaar`; no measure is rescaled. Source ambient rank `t` equals
`r+2`, so its matrix exponent `s+t/2-1` is exactly `s+r/2`.

## Support and the scalar-series argument

`equalRankSliceCoefficient_eq_zero_of_pointwise_bound` assumes a lower
determinant-order bound `Lq` wherever both `W(g)` and `φ(lastRow g)` are
nonzero. It proves that the existing equal-rank coefficient vanishes for
every index below `Lq`, independently of the inverse-character function.
The proof reduces to a quotient representative. Either a displayed factor
vanishes, or the support bound contradicts the smaller slice index.

`adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound` assumes a
lower determinant-order bound `Lh` wherever `Φ(h)` is nonzero. It proves that
the actual matrix coefficient from `AdjacentRankSpectralExpansion` vanishes
below `Lh`. On the specified group slice the support bound forces `Φ(h)=0`;
off that slice the cutoff is zero. Neither support lemma requires global
convergence.

`corankOneIntegral_eq_finiteProducts_of_coefficients` assumes these two
pointwise bounds and the actual coefficient identity, for every integer `m`,

`c(m) = ∑ k ∈ Icc Lq (m-Lh), ∑ i, a_i(k) b_i(m-k)`.

Here `c(m)` is the existing slice coefficient of the actual corank-one
integrand at zero, `a_i(k)` is the existing equal-rank slice coefficient at
zero, and `b_i(j)` is `adjacentRankMatrixSliceCoefficient F Φ χ (f i) j`.
It separately assumes genuine integrability at the same supplied complex
parameter `s` for the corank-one integrand, every equal-rank integrand, and
every shifted matrix integrand.

The equal-rank and matrix spectral expansions give sums of `a_i(k) z^k`
and `b_i(j) z^j`. The support lemmas and `hasSum_intervalConvolution`
give each finite-interval convolution its sum equal to the corresponding
product of actual integrals. Summing over the finite family and interchanging
the two finite sums identifies this scalar series with `c(m) z^m`.
The actual corank-one spectral expansion gives its sum as the corank-one
integral. Uniqueness of `HasSum` proves the asserted equality with
`adjacentRankFiniteProductValue`. The Cauchy product uses absolute
summability over integer pairs and never multiplies unrestricted bilateral
Laurent series.

## Realized model and uniform choices

`adjacentRankModel_corankOne_finiteProducts` specializes this argument to
the literal separated tensor model. Its full hypotheses retain independent
field and representation universes, a smooth first representation `σ` with
specified Whittaker functional `ℓ`, an admissible second representation `τ`
with specified functional `ℓ'` for `ψ.scale(-1)`, the supplied self-dual
additive Haar measure, and any supplied compatible quotient measure `ν`.
No irreducibility premise is imposed.

The first vector `W` belongs to the actual coefficient image of `σ`.
The ambient Whittaker function `U` is supplied with the whole-function
identity

`U(g) = adjacentRankModelIntegral
  (adjacentRankSeparatedTest Φ φ ⊗ W) g`.

The theorem does not construct this realization. It obtains from
`adjacentRankModel_corankOne_finiteConvolution` bounds `Lq,Lh`, a finite
size `N`, and a family `B` in the actual coefficient image of `τ`, all
before choosing the second vector `W'`. For each such `W'`, it chooses `f`
in the bi-smooth matrix-coefficient span of the representation on that
coefficient image, before choosing any complex `s`. The
`scaledStandardAsInverse` adapters preserve all underlying function values.
The returned support bounds have exactly the pointwise meanings above.

For every subsequent `s`, convergence of the actual corank-one integrand,
all equal-rank factors with the adapted `B`, and all shifted matrix factors
implies the finite integral product identity. The proof extracts the actual
coefficient formula from the existing model theorem and applies
`corankOneIntegral_eq_finiteProducts_of_coefficients`. It does not use an
unproved identification of the original representation with its coefficient
image.

## Scope

Every convergence premise is a genuine `Integrable` assertion. An identity of
totalized Bochner integrals supplies none of these premises. A common right
half-plane, rational continuation, model image and spanning, functional
equations, lower-to-upper induction comparison, and both parent gamma/L
certificates remain separate obligations. This conditional integral identity
does not prove either closed parent target.
