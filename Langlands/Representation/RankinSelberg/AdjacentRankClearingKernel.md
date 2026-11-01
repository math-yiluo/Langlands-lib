# Actual unramified polynomial clearing kernels

Worker 486. Internal composition of the published unramified L transport,
elementary polynomial coefficient formulas and the companion Laurent
specialization theorem. No original representation is assumed irreducible;
the field and both original carrier universes remain independent.

`EntireUniformLaurentKernel P` requires one finite integer exponent set
containing the support of every `P(u)`, and entire dependence of every
coefficient on the complex parameter. `spectralClearingKernel q P0 P1 u`
is exactly the Laurent embedding of

```text
P0 * P1.comp (C (spectralPoint q u) * X).
```

The spectral point is the existing `q^(-u)`. At zero, the kernel is exactly
`(P0*P1).toLaurent`. The polynomials may vanish; no nonzero or normalization
hypothesis is needed for this analytic and algebraic kernel construction.

## Entire coefficients and fixed support

`spectralClearingKernel_entire_uniform` proves the stated kernel property
for every natural q>1. The published positive-real-base complex-power theorem
makes `u -> q^(-u)` entire. The actual coefficient identity
`Polynomial.comp_C_mul_X_coeff` gives
`P1.coeff n * (q^(-u))^n`. Multiplication by the fixed polynomial P0 gives
finite sums of these entire functions, using the ordinary polynomial product
coefficient formula. The Laurent embedding preserves nonnegative coefficients
and has zero negative coefficients, by its actual injective map of finitely
supported coefficient functions from natural to integer exponents.

The composed polynomial has degree at most degree(P1), since the inner
polynomial has degree at most one. The product has degree at most
`degree(P0)+degree(P1)`. Thus the integer image of the fixed natural interval
through that degree contains every kernel support, before all parameters.
No parameter-dependent support is substituted for this fixed finite set.

`spectralKernel_laurent_clearing_of_real_gt` applies the companion actual
bilateral Laurent specialization theorem with this proved kernel data.
Only the entire input coefficient family and its formal Laurent clearing
on a sufficiently large positive real ray remain as inputs. The conclusion
constructs actual Laurent-polynomial outputs at all complex parameters,
with entire coefficients and one common finite support. The zero-parameter
corollary returns formal clearing by the exact original product P0*P1.

## Complete original polynomial certificates

`Padic.symmetricLPolynomial_determinantComplexPower` applies the CLOSED
published `unramifiedTwistLFactor` theorem to the literal block twist by
`F.canonicalTopologicalData.determinantComplexPower (n+1) u`. The auxiliary
scalar character is the existing unramified character at the nonzero
spectral parameter. Evaluating the published determinant-power identity
on a rank-one scalar matrix proves its exact normalized absolute-value
complex-power formula. Its determinant pullback is the actual twist
character in the conclusion.

The resulting polynomial is exactly `P.comp(C(q^(-u))*X)`. The supplied
self-dual Haar measure, character, original two representations and original
complete certificate are retained. The conclusion is the complete symmetric
relation with its compatible-measure existence witness and universal measure
and functional clauses; no scalar factor label is substituted. The theorem
has no continuation-transport or normalized-generator-transport premise.

## Remaining scope

This is internal composition of the named published inputs, not a new literal
source assertion. Existing Library pairs are unchanged. It does not construct
an entire Whittaker family, prove slice-integral analyticity, or recover
bilateral coefficients from convergent spectral sums. In particular the
real-ray hypothesis is FORMAL Laurent clearing of the actual coefficient
series; the existing rational denominator bound still needs spectral
coefficient uniqueness before it supplies that hypothesis. The final
arbitrary-character L conclusion and both unchanged adjacent-rank parent
proof records remain separate obligations.
