# Haar restriction bounds from actual right invariance

This source-free derived module proves a nonnegative Haar integral inequality
and two convergence consequences. It is intended to transfer genuine
full-matrix coefficient bounds to actual subgroup restrictions, such as the
diagonal torus. It does not deduce convergence of a raw function from
convergence of a possibly cancelling compact average.

Let `G` and `H` be groups with measurable multiplication, with `G` also having
measurable inversion, and let `iota : H ->* G` be a measurable homomorphism.
The two measures `mu` on `G` and `nu` on `H` are s-finite and left invariant.
The subgroup `K` of `G` is measurable. The function `F : G -> ENNReal` is
measurable and right invariant under `K`:

```text
F(g k) = F(g) for every k in K and every g in G.
```

The theorem `lintegral_subgroup_le_of_right_invariant` proves

```text
mu(K) · integral_H F(iota(h)) dnu
  <= nu(iota^-1(K)) · integral_G F(x) dmu.
```

Both masses in this inequality are the actual masses for the supplied
measures. The subgroup homomorphism need not be injective or have an open
image. No change of normalization, omitted Jacobian, or quotient measure is
introduced. The inequality is an inequality of extended nonnegative reals
and remains valid without finiteness or positivity assumptions on the
masses or integrals. The two group universes remain independent.

The definition `haarSubgroupFiber iota K x` is the actual set

```text
{h : H | inverse(iota(h)) x belongs to K}.
```

The theorem `measure_haarSubgroupFiber_le` shows that its `nu`-measure is at
most `nu(iota^-1(K))`. An empty fiber has measure zero. If the fiber contains
`h0`, membership is equivalent to membership of `h0^-1 h` in the inverse
image subgroup, so the fiber is one left coset. The exact left-invariance
identity for preimages of left multiplication gives its measure. This
fiber lemma requires only measurable left translations on `H` and left
invariance of `nu`; it has no s-finiteness hypothesis.

For the main inequality, write `chi` for the value-one indicator of `K`.
For each `h`, the inner ambient integral of

```text
chi(inverse(iota(h)) x) F(x)
```

is `mu(K) F(iota(h))`: left translation changes `x` to `iota(h) g`, and
right `K` invariance makes the nonzero part constant. The joint integrand
is measurable, so Tonelli exchanges the two integrals. For each `x`, its
remaining fiber integral is at most `nu(iota^-1(K))`, by the preceding
lemma. Monotonicity of the nonnegative integral proves the inequality.

The theorem `lintegral_subgroup_lt_top_of_right_invariant` additionally
assumes `mu(K) != 0`, `nu(iota^-1(K)) != top`, and finiteness of the ambient
integral. The displayed inequality then forces finiteness of the actual
subgroup integral. Compactness or openness of `K` is not an extra Lean
hypothesis; in intended topological applications those properties supply
the two stated mass conditions.

The complex consequence `integrable_subgroup_of_right_invariant` applies
this result to the extended norm of a measurable complex-valued function
`f` that is right invariant under `K`. From genuine `Integrable f mu`, and
the same two mass conditions, it proves genuine integrability of
`h |-> f(iota(h))` for `nu`. Measurability of the composite supplies strong
measurability over the separable complex target; the nonnegative inequality
supplies the finite integral of its norm.

The implementation uses Mathlib's actual left-translation invariance,
indicator integrals, Tonelli, and Bochner integrability criterion. The
module makes no p-adic, Whittaker, Fourier, matrix-functional-equation, or
gamma assertion. In particular a later diagonal-torus application must
still establish the specified invariance, measurability and mass conditions
for its own maps and measures.
