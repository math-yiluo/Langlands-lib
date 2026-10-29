# Full rectangular Schwartz Fourier equivalence and reflection

`Langlands.HarmonicAnalysis.rectangularFourierCompatibility.{uK}` proves exactly
the closed published
[`RectangularFourierCompatibilityStatement`](RectangularFourierCompatibilityStatement.md).
It retains the implicit carrier `K : Type uK`, all eight displayed typeclass
hypotheses on that carrier, every unitary additive character `ψ`, every supplied
additive Haar measure `μ`, both natural ranks `r s`, and the sole premise
`IsSelfDual ψ μ`.

The conclusion supplies an actual complex-linear equivalence `T` on
`SchwartzBruhat (Matrix (Fin r) (Fin s) K)`, with all four target clauses:
forward evaluation is `rectangularFourierIntegral ψ μ`, inverse evaluation is
the same plus integral at `-b`, the square evaluates to `Φ (-b)`, and every
displayed Fourier integrand is integrable against the supplied
`RankinSelberg.rectangularMeasure μ r s`. The target and all its imported pairs
are used unchanged.

## Supplied measure and prerequisites

The proof works directly with the nested product

```text
rectangularMeasure μ r s =
  Measure.pi (fun _ : Fin r => rowMeasure μ s).
```

This is a definitional equality of the published measures: each inner
`rowMeasure μ s` is itself `Measure.pi (fun _ : Fin s => μ.measure)`.
There is no flattening or change of coordinates. Product integration therefore
uses exactly the requested measure.

The public closing theorem obtains `SigmaFinite μ.measure` from the proved
`scalarFourierClosure K ψ μ hsd` and installs only this derived instance.
The published `rowFourierCompatibility ψ μ s hsd` supplies actual row Schwartz
Fourier partners and row square-reflection. Neither property is an additional
premise. Standard finite-product topology instances let
`rowTensorDecomposition (Fin s → K) r` apply to a matrix test function viewed as
a function of its rows.

The proof never installs a Borel-space instance on a row or matrix space. All
convergence arguments use the existing product measurable structures, scalar
Borel compatibility, finite tensor decomposition and product integration.

## Product tests and convergence

The private `productTest` bundles the pointwise product of finitely many tests
as a test on their product space. Local constancy follows by finite induction
and continuous coordinate evaluation. Its support lies in the product of the
compact topological supports of its factors. `matrixTest` specializes this
construction to row factors on the actual matrix type.

The private `character_sum` proves that the character of a finite sum is the
product of its characters. `scalarTensor_kernel` then factors the scalar-row
Fourier kernel. For any row test, `rowIntegrable` obtains its published scalar
tensor decomposition. Each scalar factor is integrable by
`fourierIntegrand_integrable`; `Integrable.fintype_prod`, multiplication by a
constant, and finite summation prove row integrability.

For a product of row factors, `rowTensor_kernel` factors the full rectangular
integrand into its row integrands. The private `rectangularIntegrable` applies
the same finite-product and finite-sum argument to the decomposition into row
tests. This proves first-integrand convergence for every matrix Schwartz test
and every output matrix, without a product Borel hypothesis.

The private `rectangularTensor_integral` applies
`integral_fintype_prod_eq_prod` to this factorization against the actual outer
product measure. The result is the product of the published plus-sign row
Fourier integrals. `rectangularIntegral_sum` proves compatibility with finite
complex linear combinations, using the convergence just established.

## Schwartz partners and square-reflection

The private `rectangularPartner` writes any matrix test as

```text
f a = ∑ j : Fin N, c j * ∏ i : Fin r, g j i (a i),
```

where every `g j i` is a Schwartz test on `Fin s → K`. Row Fourier closure
supplies an actual row test `ghat j i` for each factor. The finite sum
`k = ∑ j, c j • matrixTest (ghat j)` is a Schwartz test on the whole matrix
space, not a collection of separately controlled slices.

Tensor factorization and finite-sum linearity identify `k` with the raw
rectangular integral of `f`. Repeating the factorization and applying the
published row square-reflection law to each factor identifies the raw transform
of `k` with `f (-b)`. Thus the helper simultaneously supplies a Schwartz partner
and its reflection identity.

## Linear equivalence and inverse formula

The closing theorem chooses these partners and calls the resulting function
`F`. Their pointwise integral formula proves additivity and complex scalar
compatibility using `integral_add` and `integral_const_mul`. This gives a linear
endomorphism `L` of the matrix Schwartz space. The second partner identity
proves `L (L f) b = f (-b)`.

That square law proves injectivity by evaluating at `-b`. For surjectivity,
reflection is an actual Schwartz function, obtained by
`Hecke.TestFunction.pullback (Homeomorph.neg _)`. A preimage of `f` is
`L (f ∘ Neg.neg)`, since its image under `L` is `f`.
`LinearEquiv.ofBijective` therefore gives the required equivalence `T`.

To identify its inverse, apply square-reflection to `T.symm f` at `-b` and
simplify `T (T.symm f) = f`. This gives
`T.symm f b = T f (-b)`, hence the required raw plus-integral formula at
`-b`. Forward evaluation, square-reflection and integrability are precisely
the established identities.

All sums, products, topology arguments and product integration theorems include
empty indices. In particular, both `r = 0` and `s = 0` are covered without
an additional rank hypothesis.

## Provenance and scope

Worker 86 authored the rectangular assembly. The product-test construction
and scalar tensor convergence helpers adapt code from Worker 110's published
[`RowFourierCompatibilityProof`](RowFourierCompatibilityProof.md); Worker 110
is credited as a coauthor. The proof otherwise imports the published scalar
closure, tensor decomposition and row compatibility results by Lean name.

This is an internal derived proof of the existing interface. Its Fourier
convention and mathematical scope are inherited from the target and
[`RectangularFourier`](RectangularFourier.md), whose Markdown records the
relation to JPSS Section 6.1, printed pages 427–428, formula (6).
No separate literature theorem is asserted here. The implementation does not
establish covariance, a Fourier-conjugated action, a matrix-zeta comparison,
or a gamma/L analytic base.
