# The strict-dominant first-block JPSS Laurent identity

`Langlands.RankinSelberg.twoBlockDominantFirstBlockLaurentIdentity` proves the
existing closed proposition
`Langlands.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement`.
Its independent universes are `uF`, `uV`, and `uW`, for the field, ambient test
representation, and dependent block representation carriers. The statement
and its imported definitions are unchanged.

The original mathematical setting is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions* (1983), Section 4.9, printed pages 416–418, and
Section 4.10(2), printed page 419. The arbitrary complementary dimensions,
uniform analytic package, exact quotient measures, and coefficientwise
integration used here are derived in the imported supporting modules. This
file assembles those results into the specified closed proposition; it does
not assert that the paper states this full quantitative Lean telescope.

## Uniform analytic data

The proof introduces the complete telescope of the closed statement, with
its canonical topology, valuation, Borel structures, Haar measures and rank
relations. `compatible_standard_quotients` supplies right-invariance
certificates and existence of the two quotient measures with exactly the
normalized ambient and unipotent Haar measures in the statement.

For arbitrary full Whittaker-type representations and arbitrary supplied
functionals, `exists_uniform_analytic_inputs` chooses a real bound `C`.
For every real `u > C`, its conclusion supplies absolute convergence of the
ordinary Jacquet integral for every induced section, and one actual inverse
Whittaker functional `J` on the induced representation. The proof returns
that same `J`, its conditional nonvanishing conclusion, and its realization
identity for every section and group element. This choice precedes all
supplied quotient measures and all tests.

For each supplied compatible large and first-block quotient measure, the
analytic package gives sigma-finiteness of both and of the exact mapped
lower measure. It also gives the entire analytic conjunction of the target:
measurability of the actual upper average and lower kernel, upper product
integrability on every determinant slice, integrability of the actual lower
complex kernel, integrability of the real integral of the pointwise raw
norm, and almost-everywhere integrability of the actual rectangle fiber.
The proof returns this conjunction directly. No epsilon certificate is
used for these conclusions.

## Common epsilon witnesses and local identity

Only after returning the analytic clauses does the proof introduce a
first-block epsilon certificate. It destructures the certificate and
returns the same scalar `ζ`, polynomials `P` and `Pdual`, model scalar
condition, and full family of common normalized-generator and rational
continuation witnesses. Thus the witnesses retain every smaller rank
presentation and every pair of coefficient-model tests appearing in the
statement.

For fixed complementary `j,k`, the rank equality puts the ambient rank at
`t + (j + k + 1)`. The common witness family is specialized to smaller
rectangle dimensions `m 1 + 1 + j` and `k`, using `firstBlockSmallRank`.
Twist preservation of full Whittaker type and the standard/inverse-character
equivalence give full inverse Whittaker type for the first twisted block.
`firstBlock_small_laurent_identity` then proves the actual finite Laurent
identity at every remaining-column matrix and every base representative.
It uses both supplied normalized generators and the specialized common
functional equations. Its normalized-generator hypothesis supplies the
nonzero-functional consequence needed inside that local proof; this
assembly introduces no nonvanishing assumption on the original supplied
functionals.

## Integration and identification of the target coefficients

The proof chooses auxiliary compatible block, mixed, and lower mixed
quotient measures using their existence theorems. Closed-quotient
regularity gives sigma-finiteness of the auxiliary block quotient measure.
`lowerMeasure_isCompatible` proves compatibility of the exact mapped lower
measure already prescribed by the target. The universally supplied large
and small quotient measures remain the measures used throughout.

`firstBlock_global_laurent_identity` integrates the local finite identity.
Its inputs here are the same ordinary Jacquet functional `J`, its
realization identity, absolute Jacquet convergence, the actual lower kernel,
raw-norm-profile and fiber convergence obtained above, and the auxiliary
compatible measures. The imported bridge integrates first over the
remaining columns and then over the lower mixed zero quotient, using
genuine coefficientwise integrability. Its exact lower slice tower and
upper Jacquet unfolding produce the actual large upper and lower slice
coefficients.

The Laurent factors are exactly

```
D = Polynomial.eval₂ LaurentPolynomial.C
      (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1)) Pdual
E = LaurentPolynomial.C ((ζ : ℂ)^r * (cε : ℂ))
      * LaurentPolynomial.T d * P.toLaurent.
```

The final upper coefficient uses the statement's equality transport of the
original rectangle measure from the product measurable space to the Borel
measurable space. The private lemma
`integral_measurableSpace_transport`, proved by eliminating that equality,
identifies each inner integral with the original product-measure integral.
Pointwise equality and `integral_congr_ae` identify the coefficient series,
so the bridge's conclusion is precisely `D • Zlow = E • Zup` in the closed
statement. This transport changes neither measure normalization nor mass.

All positive block sizes, all complementary `j,k` including zero, reducible
full Whittaker-type representations, and arbitrary supplied functionals
are retained. The proof performs finite Laurent convolution and
coefficientwise integration without cancelling a polynomial on arbitrary
bilateral series or assuming any additional factor or analytic existence
premise.
