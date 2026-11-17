# Local normalization and determinant products on the partial domain

This internal module proves
`Langlands.Global.RankinSelbergGlobal.DeterminantProducts.DeterminantPowerProductStatement`
by `determinantPowerProduct`. It identifies the determinant-power factor of the
global Rankin–Selberg integrand with the product of its real, complex and finite
local factors on the partial domain. It introduces no open theorem premise.

Its provenance is the existing adelic determinant and idelic absolute value,
the finite-completion and canonical local-field normalizations, and the published
coordinate projections. This is implementation infrastructure, not a new direct
translation from an original source. Names below lie in the namespace
`Langlands.Global.RankinSelbergGlobal.DeterminantProducts` unless specified.

## Statements and conventions

Let `F` be a number field, `S` a finite set of finite places, and
`g : Points F n` an actual adelic point satisfying
`g ∈ unipotentIntegralOutside F n S`. Thus at every finite place outside `S`, its
component lies in `N_n(F_v) GL_n(𝒪_v)` in the Library's explicit sense. Then
`detNorm_product` says the global determinant norm is the product of the
normalized absolute values of the determinants of:

- `realComponent F n v g`, using the ordinary real absolute value;
- `complexComponent F n w g`, using the square of the ordinary complex norm;
- `finiteComponent F n v g` for `v ∈ S`, using
  `RankinSelberg.normalizedAbsoluteValue (padicField v).canonicalTopologicalData`.

There is no scalar correction. The finite factors outside `S` equal one.
`detPower_product`, the content of the entry proposition, applies the
positive-real complex power to this equality: for every `s : ℂ`,
`detPower F n g s` is the product of the local
`ArchimedeanLocal.detPower` functions for the same normalized absolute values and
exponent. These powers use the real logarithm, as in the published global and
local integral definitions. Their bases are strictly positive, so no complex
logarithm branch choice is involved.

Neither assertion requires compactness of the adelic quotient, cuspidal data,
character hypotheses or a convergence assumption. All natural `n`, including
`n = 0`, and empty finite or infinite indexing sets are permitted. In the
Rankin–Selberg applications `n` is a positive rank, including `n = 1`. The same
power identity applies to shifted exponents in the unequal-rank case.

## Implemented proof

`normalizedAbs_eq_completion_norm` first compares the canonical p-adic
normalized absolute value with that of `CompletionPadic.topologicalData v`.
Both equal the canonical spectral norm raised to the local extension degree by
the published normalization theorem. The latter topological data have discrete
valuation equal to the completion valuation and residue cardinality equal to
`Ideal.absNorm v.asIdeal`. The explicit definitions of normalized absolute value
and the completion norm now give equality, with zero treated separately.
This comparison uses the residue-normalized absolute value; it does not replace
it by the unraised spectral norm.

`det_mem_integers` lifts an entrywise integral matrix to the completed integer
subring. Mapping its determinant back to the completion proves integrality.
`norm_det_localIntegral` applies this to an integral invertible matrix and its
inverse. Its determinant is consequently a unit of the integer subring, so its
valuation and norm are one.

For `norm_det_isUnipotentIntegral`, use the witness that an integral right
multiple of the local matrix is upper unitriangular. That multiple has
determinant one. Multiplicativity of the norm and the integral multiplier's
determinant norm one show that the original determinant norm is one.

For `detNorm_product`, take the idele determinant of the actual adelic matrix.
Ring homomorphisms carry its determinant to the determinants of the supplied
real, complex and finite component matrices. The published idelic norm formula
splits its infinite and finite factors. The infinite factors are rewritten in
the mixed coordinates with real multiplicity one and complex multiplicity two.
The finite multiplicative support lies in `S`, by the preceding norm-one lemma,
so the finite product is exactly the product over `S`. The local normalization
comparison supplies the absolute value used by the local integral API.

`exp_log_mul` and `exp_log_prod` prove that
`exp(s * log(a))` distributes over products of positive real numbers. In
`detPower_product`, every local determinant absolute value is positive because
the component matrix is invertible. Apply these elementary identities to
`detNorm_product`. The resulting factors are definitionally the published local
determinant powers.

## Remaining obligations

This result proves the determinant normalization and product component only. It
does not factor a global Whittaker function, identify the test-function factor
at different quotient representatives, construct nonvanishing archimedean tests,
or prove the full `ArchimedeanFactorizationStatement`. Those global and
representation-theoretic obligations remain open.
