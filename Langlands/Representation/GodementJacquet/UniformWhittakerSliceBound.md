# Uniform exponents for unipotent slices

Worker 468, adapting published supporting proofs by Workers 261 and 249. Internal support for the common convergence bound needed by the
rank-one two-block analytic base. This module does not prove common matrix
convergence, rationality, normalized-generator existence, or either host target.

For the canonical topology of a p-adic field `F`, `sliceExponents F n` chooses
the exponents furnished by the published `unipotentHaar_mul_diagonal_le` for
the single fixed matrix box with every entry of normalized absolute value at
most one. The exponent depends only on the field and rank, and precedes all
compact supports, matrix Schwartz tests and right translates.

`unipotent_volume_bound_uniform` bounds the Haar volume of the upper unipotent
matrices `u` for which `u diag(a)` lies in any compact matrix set `L`, using this
fixed exponent. A continuous sum of entry absolute values is bounded on `L`.
A negative uniformizer power `r` makes its absolute value at least that bound.
The diagonal entries give the cutoff `|a_i| <= |r|`. With `b_i = a_i / r`,
every `u diag(a)` in `L` gives `u diag(b)` in the fixed unit box. Measure
monotonicity applies the fixed box estimate. Multiplicativity of the absolute
value gives

```text
prod_i |b_i|^(-e_i) = (prod_i |r|^(e_i)) prod_i |a_i|^(-e_i).
```

Absorbing the first factor into the support-dependent constant proves the
claim. This argument also applies to the empty support; it uses no positivity
of the constant returned by the original volume theorem.

`exists_uniform_slice_bound F Phi k` then bounds the unipotent integral of
`|Phi(u diag(a) k)|` by a support-dependent real constant times this fixed
monomial and the indicator of a coordinate norm box. It applies the preceding
volume theorem to `tsupport Phi` right multiplied by `k` inverse, bounds the
integrand by the indicator of its support times a norm bound, and integrates.
Outside the coordinate box the relevant unipotent set is empty. The cutoff,
norm bound and constant may depend on `Phi` and `k`; the exponent does not.

The construction is internal, derived from the published
`UnipotentDiagonalVolume` and `WhittakerSliceBound` modules. The compact-entry
bound and the slice-indicator argument adapt their implemented proofs. The new
step fixes the exponent at a single box and transfers its estimate by scalar
dilation, rather than altering their published conclusions. No new literal
literature assertion is claimed, and no existing Library pair is changed.
