# Cuspidal-factor decay from the constant-term tail estimate

This internal lemma implements the cancellation and tail part of VIII.3.1
for abstract parabolic data. It uses the full constant-term estimate
through `ConstantTermEstimate.tail`, so no exact invariance under a
compact covering subgroup is required.

`CuspidalFactorTailBound` says that for every real Levi exponent `d` and
nonnegative real cutoff exponent `p`, there is a finite nonnegative
constant bounding the norm of the normalized cuspidal factor at `(a,m)`
by

```text
c δ(a)^(-1) t(a)^(-p) ΞM(m) (1 + σM(m))^(-d)
```

uniformly for `a` in the specified set and all Levi points `m`.
Norms and kernels in Lean are expressed in the extended nonnegative
reals, with the scalar factors inserted by their canonical coercions.

`cuspidalFactorTailBound_of_constantTermEstimate` proves this assertion
under the following explicit inputs: the conjugation modulus relation;
the full constant-term estimate; positive ambient Xi and nonnegative
ambient height; the height-product bound; a measurable truncation `Γ`;
finite Schwartz decay seminorms of `f`; integrability and vanishing of
the full unipotent integral of `f(m u)` at every Levi point; and a positive
cutoff `t(a)` on a subset `V(a)` containing the complement of the expanded
truncation.

The implemented proof first uses
`IsConjModulus.enorm_integral_conj_le`: vanishing of the full integral
turns the truncated integral into its complementary tail and the change
of variables contributes `δ(a)^(-1)`. Bound the function on that tail
by one finite Schwartz seminorm times the weighted Xi kernel. The
constant-term tail estimate bounds the normalized lower integral, and
the product of its finite constant with that seminorm gives the required
constant.

The cutoff subset need not be measurable or compact-conjugation
invariant. The lemma neither proves the actual-point constant-term
estimate nor supplies the geometric height cutoff. For intrinsic
actual cuspidal functions, convergence and vanishing of the proper
opposite-radical integrals are supplied separately by the proved
intrinsic-kernel transport.
