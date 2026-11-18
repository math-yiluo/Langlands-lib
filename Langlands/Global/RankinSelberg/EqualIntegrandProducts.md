# Equal-rank integrand products from paired Whittaker products

This internal module proves
`Langlands.Global.RankinSelbergGlobal.EqualIntegrandProducts.PairedWhittakerIntegrandProductStatement`
by `pairedWhittakerIntegrandProduct`. It derives the equal-rank pointwise
integrand identity from an explicit paired global Whittaker product and an
explicit test-function product, while handling the local quotient
representatives and determinant conventions. The global Whittaker product
remains a premise; the full global theorem is not proved here.

The module is implementation infrastructure derived from the published global
and local integral, quotient, coordinate and test-data definitions and the
proved determinant product in `ArchimedeanDeterminantProducts`. It claims no new
direct translation from an original source. Unqualified names below are in the
namespace `Langlands.Global.RankinSelbergGlobal.EqualIntegrandProducts`.

## Local representative and integral adapters

`determinantWeight_eq_detPower` identifies the local Rankin–Selberg complex
power `(abv(det g) : ℂ)^s` with the real-logarithm expression in
`ArchimedeanLocal.detPower`. Since `g` is invertible, its absolute determinant
value is strictly positive, and the complex logarithm of that positive real is
the real logarithm. The order of the two complex factors in the exponent is
then commuted.

`local_detPower_unipotent_mul` proves that left upper-unipotent multiplication
preserves `ArchimedeanLocal.detPower` for any supplied real-valued function of
the determinant. It only uses that the unipotent determinant is one. No
subadditivity requirement is imposed on this function; in particular the lemma
applies to the square of the usual complex norm.

`equalIntegrand_mk_of_pair_invariant` takes arbitrary functions `W`, `W'` whose
product is invariant under simultaneous left upper-unipotent translation. For
any row test, their `ArchimedeanLocal.equalIntegrand` at the class of `g` is the
expected expression evaluated at `g`, rather than at the quotient's chosen
representative. The chosen representative differs from `g` by a left
upper-unipotent matrix. The product hypothesis, invariance of the last row and
the determinant lemma identify the two expressions.

For actual bundled standard/inverse Whittaker functions,
`equalIntegrand_eq_rankinSelberg` identifies the representative formula with
the descended `RankinSelberg.equalRankIntegrand`. It evaluates the descended
function at the class of the quotient's chosen representative and uses
`Quotient.out_eq`. `equalIntegral_eq_rankinSelberg` integrates this equality for
any supplied quotient measure; it makes no convergence assertion.

`padic_testData_integral` and `padic_testData_dualIntegral` specialize the integral
adapter to `EqualLocalTestData`, using the canonical p-adic topology and Borel
spaces and `equalPadicQuotientMeasure`. The ordinary raw local integrand
integrates to `D.integral`. The raw dual integrand, with both Weyl–inverse-
transpose dual functions and `D.Φhat`, integrates to `D.dualIntegral`. These
are the existing measures and dual functions, with no additional scalar or
normalization. They give the finite local integral-identification clauses used
in `EqualPointwiseFactorizationStatement`.

## Product statement

Let `F` be a number field, `r` a natural number and `S` a finite set of finite
places. Supply global functions `W`, `W'`, a row test `Φ`, a scalar `κ`, and real,
complex and `S`-indexed finite local functions and row tests. Assume:

- the product of each pair of local Whittaker functions is invariant under left
  upper-unipotent multiplication;
- for every actual adelic point in `unipotentIntegralOutside F (r+1) S`,
  `W(g) W'(g)` is `κ` times the product of the corresponding local paired values;
- `Φ` is exactly the `integralOutside` indicator times the product of the local
  row tests at their real, complex and finite coordinates.

Then, for every `s : ℂ` and every class in
`unipotentIntegralClasses F (r+1) S`, the global equal-rank Whittaker integrand is
`κ` times the product of the local equal-rank integrands at precisely the
published `realQuotientProjection`, `complexQuotientProjection` and
`finiteQuotientProjection` of that class. The finite determinant powers use the
canonical residue-normalized absolute values. The scalar is unchanged.

No nonzero assumption on `κ`, Schwartz assumption on the supplied test functions,
character data or convergence hypothesis is needed for this pointwise
bookkeeping result. Rank `r = 0`, meaning `GL_1`, and empty place sets are
included. Local invariance and the supplied paired and test products are
explicit hypotheses, not conclusions of the module.

## Implemented product proof

`lastRow_mem_integralOutside` shows that the last row of an adelic point in the
partial domain lies in `integralOutside`. At an off-`S` finite place, the domain
witness gives an integral right multiplier that makes the component upper
unitriangular. Therefore its last row is the last row of the inverse integral
multiplier and has integral entries. The three coordinate lemmas identify the
real, complex and finite coordinates of the global last row with the last rows
of the component matrices.

In `pairedWhittakerIntegrandProduct`, evaluate the supplied paired global
Whittaker product at the representative of the global quotient class. The last
row lemma removes the indicator from the supplied test product. Apply
`DeterminantProducts.detPower_product` to the determinant factor. At each local
quotient projection, `equalIntegrand_mk_of_pair_invariant` replaces the chosen
local representative by the component of the global representative. The
coordinate lemmas and finite-product distributivity identify all factors, and
commutative ring algebra completes the identity.

## Remaining obligations

To apply this result to the ordinary and dual halves of the global target,
one still must supply the appropriate paired global Whittaker products with
the same `κ`, the required local restrictions and nonvanishing data, and the
ordinary and Fourier test products. The two local integral adapters do not
supply those global products. In particular neither
`EqualPointwiseFactorizationStatement` nor the unconditional
`ArchimedeanFactorizationStatement` is proved by this module.
