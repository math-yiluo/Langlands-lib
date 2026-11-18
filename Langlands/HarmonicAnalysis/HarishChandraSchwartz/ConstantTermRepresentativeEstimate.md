# The scalar constant-term estimate on representatives

Worker 248, Task 5460. `ConstantTermRepresentativeEstimateStatement.{u}`
is a Prop-valued statement at arbitrary universe `u`, proved by
`constantTermRepresentativeEstimate`. It isolates the scalar-integral
argument used internally in the published `constantTermEstimate_of_bounds`,
before that theorem applies compact invariance and a double-coset cover.

For a measurable group, subgroups `M,U`, a measure on `U`, a positive
character `delta` on `M`, nonnegative height `sigma`, and nonnegative Levi
weight `XiM`, assume the published abstract predicates `UnipotentXiBound`,
`SigmaProductBound`, `XiLowerBound` and `UnipotentWeightIntegrable`, with
a common set `S` of representatives. The upper-bound auxiliary weight `e`
and the integrated weight `w` are nonnegative, and
`e(m) sqrt(delta(m)) <= eM(m)` on `S`. The conclusion is the normalized
constant-term inequality on `S` for every real target exponent, with a
uniform real ambient exponent and a finite nonnegative constant chosen
before the representative. The character takes values in positive
nonnegative-real units, as in the existing abstract interfaces.

The implementation chooses `r` to dominate the target exponent, the
integrability exponent, and zero. It uses the published scalar inequality
`one_add_rpow_neg_le` to split the product-height decay into independent
Levi and unipotent decay factors. The upper spherical bound cancels its
polynomial growth against the additional ambient exponent. Monotonicity
of the lower integral and the finite weighted integral give the integrated
constant. The modulus comparison and lower spherical bound then give the
Levi weight with the requested decay. Constants in the two bounds are
replaced by their nonnegative maxima, and the finite lower integral is
converted to an NNReal constant only after finiteness has been proved.
This is the same proof as the representative part of the existing full
abstract theorem; its compact-cover argument is not repeated.

Provenance is derived from the already implemented proof and Waldspurger's
Proposition II.4.5, printed pp.262-263. The four analytic bounds remain
explicit premises of this abstract helper. The module supplies no actual
rational-group analytic bound or proof of the final actual constant-term
target. Source: Waldspurger (2003), registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
