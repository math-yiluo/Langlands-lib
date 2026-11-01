# Actual uniformizer-torus sums from ambient convergence

This internal derived module specializes the Haar restriction inequality to
uniformizer powers in the actual diagonal torus. It turns an ambient absolute
integrability bound into a genuine discrete torus norm-summability bound for
functions fixed by an actual principal congruence subgroup. It does not assume
or prove a raw Whittaker matrix-integral bound.

The definition `uniformizerTorusHom n pi` sends the integer exponent vector
`e : Fin (n+1) -> Z`, viewed as a multiplicative group, to the literal matrix
`Iwasawa.torus pi e`, whose diagonal entries are `pi^(e i)`. The exponent
lattice has the full discrete measurable space and counting Haar measure.
It is countable, so that measure is s-finite. The map is a genuine group
homomorphism by the diagonal homomorphism and the integer-power addition
identity. It is measurable because its domain is countable with measurable
singletons.

The algebraic theorem `uniformizerTorusHom_preimage_principalLevel` applies
to any field with a valuation relation, any actual uniformizing element,
every rank index `n >= 0`, and every principal level `a >= 0`. It states
that the inverse image of the actual principal subgroup is the singleton
identity exponent vector. The proof first places a principal element in
the integral subgroup. Entries of both its diagonal matrix and its inverse
are integral, so every uniformizer power on the diagonal is an actual
integral unit. The published uniqueness of uniformizer cosets modulo
integral units forces each exponent to be zero. Conversely, the zero
exponent gives the identity matrix in every principal subgroup. Thus the
inverse-image counting mass is exactly one, without any Jacobian or
unspecified Haar constant.

In the canonical p-adic setting,
`integrable_uniformizerTorus_of_principalFixed` assumes a measurable complex
function `f` on `GL_(n+1)` fixed on the right by the actual principal subgroup
at level `a`, together with genuine ambient integrability for the existing
`generalLinearHaar F.Carrier n`. It proves genuine integrability of

```text
e |-> f(Iwasawa.torus pi e)
```

for counting Haar on the exponent lattice. The principal subgroup has
strictly positive ambient measure because it is open and contains the
identity. Its inverse-image counting measure is finite by the preceding
singleton identity. The theorem then applies
`integrable_subgroup_of_right_invariant` to the actual homomorphism and
these actual measures. No convergence of an average is used to infer
convergence of its integrand.

The corollary `tsum_enorm_uniformizerTorus_lt_top_of_principalFixed` states
that the sum over all integer exponent vectors of the extended norm of
`f(Iwasawa.torus pi e)` is finite. It is the same genuine integrability
bound, rewritten by the counting integral formula. Exponents are tagged
multiplicatively in Lean and converted to their ordinary additive vector
only at the `Iwasawa.torus` argument.

The module retains arbitrary canonical p-adic fields in any universe,
all `n` including zero, the actual uniformizing-element premise and the
unchanged normalized ambient Haar. Its provenance is source-free composition
of HaarRestriction, the actual principal/integral entry conditions, and the
published uniformizer-coset uniqueness theorem from IwasawaTorusPartitionProof.
For an eventual application to a full-matrix coefficient integrand, its
measurability, right principal invariance and ambient convergence must still
be supplied. No Whittaker asymptotic, matrix functional equation, or gamma
comparison is asserted here.
