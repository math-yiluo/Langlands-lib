# The actual finite epsilon product as an entire nonvanishing function

This internal derived unit makes the finite epsilon product callable without
choosing an exceptional set. Its factors are precisely `finiteEpsilon`, hence
the expressions in the published `HeckeGlobalFunctionalEquationStatement`,
with the supplied actual finite additive components and supplied self-dual
Haar measures. The number field has arbitrary universe `u`.

`finiteEpsilonLogSlope` is minus the sum of the actual additive conductor
and actual multiplicative conductor, multiplied by the logarithm of the
residue cardinality, as a complex number. The local theorem
`finiteEpsilon_eq_zero_mul_exp` is the existing `epsilonAt_eq_zero_mul`
after unfolding the actual conductor choices and commuting scalar factors.
It retains the existing spectral convention and every supplied measure.
The local epsilon is entire by `epsilonAt_differentiable`, and nonzero by
`epsilonAt_ne_zero` with the proved specifications of the actual conductors.
The latter theorem applies even to arbitrary regular additive Haar measures;
we use it at the supplied self-dual measure.

`finiteGlobalEpsilon` is the unordered product of these local factors.
`finiteGlobalEpsilon_eq_prod` identifies it with the product over any finite
set outside which every local factor is one at every parameter. Thus the
value is independent of the particular valid exceptional set.
`prod_finiteEpsilon_eq_zero_mul_exp` multiplies the local spectral laws and
combines the finitely many exponentials into the exponential of the sum.

The global results take the original continuous nontrivial global additive
character trivial on the diagonal, every supplied actual finite component,
every supplied self-dual local measure, and every supplied nonzero real and
complex scale satisfying the published component predicates.
`exists_finset_finiteEpsilon_eq_one` derives the needed finite exceptional
set from these global data. Finite conductor support is a proved input,
not a new assumption of these results.

With that set fixed for all spectral parameters,
`finiteGlobalEpsilon_hasProd` gives the exact unordered product at every
parameter. `finiteGlobalEpsilon_differentiable` differentiates the finite
product of entire local factors, and `finiteGlobalEpsilon_ne_zero` uses
their nonvanishing. Its reciprocal is therefore also entire, and
`finiteGlobalEpsilon_meromorphic` supplies the meromorphic interface.
`exists_finiteGlobalEpsilon_spectral` records a single finite sum of actual
conductor slopes that gives the product's exponential spectral dependence
at every parameter, centered at zero.

The provenance is direct composition of the existing local Gauss-epsilon
spectral and nonvanishing theorems, Mathlib's finite-product calculus, and
the actual global conductor-support theorem. No new assertion from the
literature is required. This unit proves properties of the finite epsilon
factor. It does not prove continuation of the Hecke Euler products or the
global functional equation.
