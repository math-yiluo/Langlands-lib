# Matched actual original and model-star determinant coefficients

This derived prerequisite implements the determinant coefficient form of
JPSS Section 6.3, formulas (10) and (14), using the actual model-star
restriction and one matched finite outer convolution. It preserves the
same finite original model vectors and matrix coefficient functions in
both formulas.

All topological and valuation structures are those of the supplied
canonical p-adic field. Write `n=r+1`, `Q=N_n\GL_n`, and let `nu` be any
quotient measure compatible with the unchanged general-linear and
upper-unipotent Haar measures. For supplied finite inverse Whittaker
functions `B_i` and group functions `f_i`, define

```text
A_i(k) = equalRankSliceCoefficient(T,nu,psi,W,B_i,phi,k),
b_i(j) = adjacentRankMatrixSliceCoefficient(F,Phi,chi,f_i,j).
```

`AdjacentRankCoefficientConvolution` is a proposition asserting genuine
integrability of every determinant slice of the actual corank-one
integrand at parameter zero, integrability of every equal-rank quotient
slice and group factor, and the coefficient formula

```text
sliceCoefficient(T,nu,corankOneIntegrand(psi,U,W',0),m)
  = c * sum_(Lq <= k <= m-Lh) sum_i A_i(k) b_i(m-k).
```

The supplied scalar `c` is explicit. The proposition records actual
coefficients and genuine integrability; it makes no analytic continuation
claim.

`adjacentRankCoefficientConvolution_of_shell` proves this assertion
without making any new finite choices. Its premises are a supplied outer
convolution for every shell and the pointwise equality of the corank-one
determinant indicator with `c` times the before-shell inner integral.
The genuinely integrable before-shell product kernel makes its inner
integral integrable on the quotient. Multiplication by `c` and the
indicator equality prove genuine integrability on each determinant
slice. Integrating that same equality, moving `c` out of the integral,
and applying the supplied outer identity proves the coefficient formula.

For a smooth, full Whittaker-type first representation `sigma`, take a
standard functional `ell`, its actual model vector `W`, and a Whittaker
function `U` explicitly realized by the separated rectangular test
`Phi tensor phi tensor W`. Let `tau` be an admissible second
representation, with a specified functional for `psi.scale(-1)`.
The row test `phiHat` is an actual plus Fourier partner for `phi` with
respect to the same supplied character and scalar self-dual Haar measure.
Put

```text
PhiD(X) = PhiHat(-X),
WD(g) = W(w_n*iota(g)),
UD(g) = U(w_(n+1)*iota(g)),
cD = chi^-1(det(-I_n)).
```

The transformed functions are the actual published dual model map or
dual function equivalence, recast along the published character equality
to the standard character `psi.scale(-1)`. No equality between an
original carrier and its coefficient image is asserted.

`adjacentRankModel_matchedCoefficientConvolution` chooses four actual
lower support bounds, one finite size `N`, and one family `B` in the
specified actual coefficient image of `tau` before the second vector
`W'`. It then chooses one family of actual bi-smooth matrix coefficients
`f_i` of that coefficient image's right-translation representation before
all determinant orders. The two coefficient assertions above hold, with
their respective pointwise support bounds:

* The original assertion uses `psi,W,U,W',Phi,phi,chi,B_i,f_i` and `c=1`.
* The transformed assertion uses
  `psi.scale(-1),WD,UD,dualModelLinearMap(W'),PhiD,phiHat,chi^-1`,
  the family exactly `dualModelLinearMap(B_i)`, the functions exactly
  `coefficientIota(f_i)`, and the scalar exactly `cD`.

The proof calls `adjacentRankShell_matchedFiniteConvolution` once for the
original tests and their actual Fourier transforms. Its original
before-shell assertion is identified with the actual corank-one indicator
by `adjacentRankModel_corankOneSlice_eq_before`. Its transformed assertion
is identified by the literal fixed-character
`adjacentRankModelStar_corankOneSlice_eq_before`. Applying the
coefficient transfer theorem twice preserves the exact witnesses; no
second finite-family choice is made.

The representation carriers and field retain independent universes.
Reducible representations, possibly zero specified functionals, and
actual inner rank one are included. Carriers have only algebraic additive
and complex-module structures. The displayed realization of `U` is
explicit intermediate data and is not a premise added to either parent
gamma/L statement.

The registered original is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in preceding work; printed
pp.435–437 were visually reread for the matched and model-star
calculations. Formula (10) follows from complementary determinant
orders. On p.437 the source transforms the same finite family, reflects
the square Fourier test, inverts the determinant character and retains
the sign scalar before (14). The earlier bounded registered-source and
correction-note audit found no JPSS-specific registered erratum.

This is the actual determinant-coefficient step, with genuine convergence
on every determinant slice. Summing the coefficients on a common
half-plane, global rational product formulas, matrix analytic witnesses,
functional equations, model realization and both parent factor
conclusions remain separate obligations.
