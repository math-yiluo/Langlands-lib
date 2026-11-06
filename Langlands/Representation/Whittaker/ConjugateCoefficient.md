# Conjugate Whittaker functionals and positive coefficient products

This is an internal derived construction on the published algebraic Whittaker
functional and coefficient spaces. It applies to a subgroup `N` of an arbitrary
group, a unitary complex character `θ` of `N`, two representations `π` and `σ`,
and an equivariant conjugate-linear equivalence `E` between their carriers.
The group and the two carriers have independent universes.

`conjugateFunctional` sends a `θ`-equivariant functional `ℓ` on `π` to
the linear functional

`w ↦ conj(ℓ(E.symm(w)))`

on `σ`. The two conjugate-linear operations make this functional complex
linear. Equivariance of `E` transports the action, and the norm-one hypothesis
on `θ` identifies its complex conjugate with its inverse. Thus the output
belongs to `functionals N θ⁻¹ σ`. Surjectivity of `E` and injectivity of complex
conjugation prove that a nonzero input has nonzero output.

`coefficient_conjugateFunctional` identifies the coefficient at `E(v)` with the
complex conjugate of the original coefficient at every group element.
`coefficient_mul_conjugateFunctional` then uses the elementary complex identity
`z * conj(z) = ‖z‖²`. For a nonzero functional, choose a vector on which it does
not vanish. Evaluating at the identity gives the strictly positive real part
in `exists_coefficient_product_pos`.

For an admissible representation with an invariant positive Hermitian form
`b`, assume that every open subgroup of the topological group contains a
compact open subgroup. `hermitianDualFunctional` applies this construction to
the published conjugate-linear equivalence `b.smoothDualEquiv`, whose target is
the actual smooth contragredient. Its equivariance is the published
`b.toSmoothDual_apply_action`. The last three theorems give nonzeroness,
coefficient conjugation, and the squared-norm product in this specialization.
There is no norm or topology on either representation carrier.

The provenance is the direct composition of `Whittaker.Algebraic` and
`Unitary.HermitianDual` with elementary complex conjugation. The conclusions
are pointwise coefficient identities. They do not assert positivity of an
integral, existence or nonvanishing of a residue, or the equal-rank local
L-factor formula.
