# Equal-rank factorization from normalized infinite Whittaker tests

`equalInfiniteWhittakerReduction` proves
`EqualInfiniteWhittakerReductionStatement.{u,uQ}`. Its single premise is
`EqualInfiniteWhittakerTestStatement.{u,uQ}` and its conclusion is the
published `EqualArchimedeanFactorizationStatement.{u,uQ}`. The two universes
remain independent. The reduction includes `r = 0`, which denotes `GL₁`,
and an empty finite set `S`.

## Retained premise

Take the equal-rank target's number field with compact `AdeleQuotient F`,
unitary adelic character trivial on the number field, cuspidal realizations
and contragredients, spectral presentations with irreducible admissible
finite components, exceptional-set containments and finite additive support
in `S`, and the prescribed real and complex character and representation
parameters. The premise uses the canonical finite character components at
`S`. It quantifies over supplied standard and inverse-character
Whittaker functionals on the factors of the two presentations and finite
reference tuples of functional value one.

For those fixed finite reference tuples, the premise supplies two tensors in
the actual infinite source spaces and a nonzero scalar `κ`. For each real and
complex place it supplies two functions satisfying the target's actual
`IsRealPlaceWhittaker` or `IsComplexPlaceWhittaker` predicate, for the
character and its inverse respectively, together with local Schwartz
functions and quotient measures. On `unipotentIntegralOutside`, the paired
global residual for the normalized reference vectors equals `κ` times the
product of those local pairs. Each residual is evaluated at the point
retaining all infinite coordinates and identity at every finite place.
The premise also supplies both archimedean nonvanishing clauses. The
ordinary product and the dual product of infinite-place integrals each
have a nonzero value on every right half-plane, possibly at different
parameters.

## Implemented proof

1. At each place in `S`, `exists_tests` chooses one `EqualLocalTestData`
   with ordinary and dual nonvanishing for the given self-dual measure.
   `factorCoefficient` and `inverseFactorCoefficient` transport its two
   coefficient functions exactly to the presentation factors and give the
   normalized finite references. Apply the infinite premise to these
   references to choose the infinite tensors. Tensoring the prescribed
   coefficient vectors with these tensors gives the two actual global
   vectors, spherical outside `S`.
2. `ordinaryDualFiniteProduct` factors the paired global Whittaker
   functions into the prescribed coefficients at `S` and the residual
   product. For the dual identity, apply the infinite premise at
   `Unfolding.dualPoint`. The dual point preserves the partial domain and
   projects to the local dual argument, so this gives the dual residual
   product with the same `κ`.
3. `localFourierTestAssembly` builds the actual Schwartz–Bruhat function
   standard outside `S` from the archimedean Schwartz functions and the
   finite test functions. It gives the ordinary and Fourier products with
   coefficient one, using the published rectangular self-dual measure
   comparison. The Fourier factors at `S` are the partners from the same
   `EqualLocalTestData`.
4. The opposite-character pairs are invariant on the left by the local
   unipotent groups, and this invariance persists under the dual argument.
   `pairedWhittakerIntegrandProduct` applies to both products, incorporating
   the determinant weights and identifying the actual quotient integrands.
   The local p-adic quotient integrals are the integrals of the chosen
   test data by `padic_testData_integral` and
   `padic_testData_dualIntegral`. This proves the Library's
   `EqualPointwiseFactorizationStatement`.
5. `equalArchimedeanFactorizationReduction` integrates both products
   using the published `UnipotentClass.unipotentClassProductStatement`.
   The common nonzero constant is the product of `κ` and the
   quotient-measure scalar.

This is an internal reduction of the equal-rank part of the factorization
step in Cogdell's proof of Theorem 4.1. Its formal inputs are the Library's
reduction and concrete tensor, local test, and measure interfaces. The
construction of the infinite residual products and the associated
archimedean nonvanishing data remains the premise of the theorem.
