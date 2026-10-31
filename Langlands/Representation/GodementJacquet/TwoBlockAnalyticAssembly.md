# Assembly of the full two-block matrix analytic predicate

This internal derived result assembles the previously published linear and
Laurent-module operations into the full matrix analytic predicate. It is a
conditional assembly theorem. It does not construct the analytic inputs for
an induced representation and does not prove the closed two-block
analytic-induction statement.

The representation `π` may be any actual representation at the proposed total
rank. The two block representations have positive ranks `m i + 1`, their
dependent complex carriers, and supplied group measures `μ i`. The total
representation has its own supplied measure `μind`. The field, block carriers
and total carrier have independent universes. There is no assumed
irreducibility or identification of coefficient spaces.

`TwoBlockMatrixGeneratorInputs` is the conjunction of three actual analytic
inputs for `π`:

- One right half-plane of shifted integrability works for all full-matrix
  tests and all individual smooth coefficient generators of `π`.
- Every such test and generator has an actual shifted rational value in the
  product of the two entire block Laurent value modules.
- The product of any two actual shifted rational values from individual
  smooth block coefficients belongs to the entire Laurent value module of
  `π`.

`matrixAnalyticAssertions_twoBlock_of_generators` assumes this input predicate
and the ordinary full matrix analytic predicate for each block. It proves the
full predicate for `π`, with the product polynomial.

The first bound is chosen before all tests, coefficients and spectral
parameters. Every shifted rational-value hypothesis is the published guarded
relation: it includes actual integrability and rational continuation with
reduced-denominator nonvanishing. All supplied measures, shifts and the common
parameter `q` remain unchanged. The explicit condition `1 < q` is used for
rational-continuation uniqueness.

The implemented proof first extends rational existence and product-module
membership to the entire complex coefficient span by
`exists_hasShiftedRationalValue_mem_of_generators`. It extends the one common
integrability half-plane by `matrixConvergesOnRight_iff_generators`. The
forward Laurent-span containment follows from
`zetaSpan_matrixRationalValues_le_of_generators`, which uses uniqueness to
identify every actual rational value with the constructed value. The reverse
containment follows from
`zetaSpan_matrixRationalValues_mul_le_of_generator_products`; the existing
block analytic predicates supply its generator-rationality premises.
Finally, `normalizedGenerator_twoBlock_of_span_eq` transports the two block
normalized generators through the proved equality of both Laurent spans.
Its conclusion includes constant coefficient one for the product polynomial
and the exact reciprocal-product generator.

All provenance is internal, from `AnalyticData`, `ZetaLinear`,
`ZetaCoefficientGenerators` and `ProductGenerators`. The construction of the
common bound, the noncompact product-integral formula, and reverse realization
for actual induction remain separate obligations.
