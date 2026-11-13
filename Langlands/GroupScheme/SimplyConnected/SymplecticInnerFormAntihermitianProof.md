# Symplectic inner forms are groups of antihermitian division forms

`symplecticInnerFormAntihermitian` proves exactly the published proposition
`Langlands.GroupScheme.SymplecticInnerFormAntihermitianStatement` at every
universe parameter `u`.

For the supplied inner-form presentation of `G`, the theorem
`symplecticInnerFormInvolution` constructs a finite-dimensional central
simple algebra `A`, a first-kind involution `τ` with a finite Galois
standard symplectic splitting chart, and an isomorphism from `G` to
`normOneGroup τ`. Its proof descends the standard alternating adjoint
involution along the twisted semilinear Galois action, and compares the
groups on every relative test scheme before fpqc descent.

The theorem `symplecticInvolutionAntihermitian` applies to that chart.
It supplies the central division algebra `D`, its positive degree,
the nonzero matrix size `m`, the equalities `m * degree = 2 * n` and
`finrank K D = degree ^ 2`, and the first-kind involution `σ` with
symmetric-space dimension `degree * (degree + 1) / 2`. It also supplies
an invertible trace-valued antihermitian Gram matrix `H` and an algebra
equivalence `φ : A ≃ₐ[K] Matrix (Fin m) (Fin m) D` satisfying
`φ (τ x) * H = H * σ.matrix (Fin m) (φ x)`.

The group-scheme comparison `normOneGroupAlgEquivIso` turns this algebra
equivalence and adjoint compatibility into an isomorphism from
`normOneGroup τ` to `σ.symplecticGroup H`. Composing it with the first
isomorphism gives the requested isomorphism from `G`. Every numerical,
division-algebra and antihermitian witness is carried directly from
the classification conclusion into the target.

The implemented proof composes these constructions without adding
hypotheses. In particular, it retains characteristic two, the
trace-valued condition in `σ.IsAntihermitian`, arbitrary ambient
universe and an isomorphism of actual group schemes over `Spec K`.
