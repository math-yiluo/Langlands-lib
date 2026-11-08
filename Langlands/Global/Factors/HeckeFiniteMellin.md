# Actual finite Hecke Mellin series and their Fourier comparison

This internal assembly removes the additive-conductor support premise from the
actual finite Fourier divisor-series comparison. It applies to every number
field in arbitrary universe `u` and every actual Hecke character. The Fourier
result accepts the original continuous nontrivial global additive character
trivial on the diagonal, every supplied actual finite additive component,
every supplied self-dual local Haar measure, and every supplied nonzero real
and complex additive scale satisfying the published component predicates.

`finiteMellin chi s` is the unordered divisor sum of the actual finite
Euler-test shell weights. The sum ranges over all finitely supported integer
functions on the finite places. Its coefficient is the product of the local
weights over the support of that function. `exists_finiteMellin_hasProd` gives
absolute summability and identifies this sum with the exact unordered product
of the published finite `lFactor` functions in a right half-plane, by the
existing `exists_hasProd_shellWeight` theorem.

`fourierFiniteMellin chi psif mu S s` is the analogous divisor sum of the
actual Fourier-transformed Euler-test shell weights for the inverse local
multiplicative character. Its coefficient retains the product over
`S` union the divisor support. In particular all exceptional zeroth factors
remain, even when they vanish. The transform uses precisely each supplied
`(mu v).val.measure`; no common representative of the self-dual measures is
chosen.

`exists_finiteMellin_common_halfPlane` first applies
`exists_finset_additiveConductor_eq_zero` to the supplied global data. This
finite support follows from the exact positive-sign additive product formula
and the lattice arithmetic proved by Worker 1798. It is not an additional
premise. The existing Fourier divisor theorem enlarges that exceptional set
by the finite multiplicative ramification set. The original series for the
character and its inverse, and the Fourier series, all converge absolutely
on the maximum of their three right half-planes. On this common half-plane
the theorem gives the original and inverse finite Euler products and

```
HasProd (fun v => finiteEpsilon chi psif mu v (1-s) * finiteL chi_inverse v s)
  (fourierFiniteMellin chi psif mu S s).
```

The same set `S` works at every complex spectral parameter for epsilon
triviality and for the Fourier weight's zeroth term to equal one outside `S`.
The epsilon family therefore has unordered product equal to its finite
product over `S`. Multiply that product by the inverse-character Euler
product and use uniqueness against the Fourier `HasProd`. This proves

```
fourierFiniteMellin chi psif mu S s
  = (product over v in S of finiteEpsilon chi psif mu v (1-s))
      * finiteMellin chi_inverse s.
```

No exceptional coefficient or epsilon factor is divided out. The argument
`1-s`, integer exponents, uniformizers, local spectral variables and p-adic
Haar normalizations are the existing ones from `HeckeDivisorEulerProduct`.
The provenance is direct composition of those proved finite-series results
with the actual conductor-support adapter. This unit does not identify these
sums with adelic integrals or prove archimedean Mellin formulas, meromorphic
continuation or the global functional equation.
