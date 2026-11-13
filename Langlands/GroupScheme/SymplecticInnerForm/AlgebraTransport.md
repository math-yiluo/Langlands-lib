# Transport of involution isometries through algebra equivalences

This internal construction supplies the algebra-to-group comparison used in
the classification of symplectic inner forms. It does not assert the existence
of an algebra equivalence or a division-form model.

An algebra equivalence induces tensor-unit equivalences over the relative
global sections of every test scheme. Tensor transport commutes with every
test restriction, so the natural point equivalence gives an actual
isomorphism of algebra-unit group schemes.

For involutions `τ` on `A` and `ν` on `B`, suppose an algebra equivalence
`e : A ≃ₐ[K] B` and an invertible Gram element `H` satisfy
`e(τ(x)) H = H ν(e(x))` for all `x`. Tensor induction extends this identity
to every commutative coefficient algebra. Multiplying the identity on the
left by the transported `x` and cancelling the invertible scalar extension
of `H` shows that `x τ(x) = 1` is equivalent to
`e(x) H ν(e(x)) = H`.

For central simple algebras, the unconditional reduced norm is preserved by
the algebra equivalence on every tensor unit. Consequently the actual
reduced-norm characters commute with the ambient group-scheme isomorphism.
When `B` is a matrix algebra over a finite-dimensional central division
algebra `D` and `ν = σ.matrix n`, the two isometry equations describe exactly
the published involution-isometry and division-form unitary subgroups.
Their reduced-norm-one subgroup functors therefore agree under the ambient
isomorphism on all relative tests, including nonaffine tests.

`normOneGroupAlgEquivIso` applies the uniqueness of a represented subgroup to
this equality and constructs
`normOneGroup τ ≅ σ.symplecticGroup H`. The accompanying inclusion-square
theorem identifies its ambient map with tensor transport by `e`. Neither
antihermitian type nor a symmetric-dimension condition is needed for this
comparison: those are additional properties supplied by the separate
division-form classification.

The construction is derived from the published finite-algebra-unit
representability, tensor functoriality, involution base change,
`CentralSimple.reducedNormUnits_algEquiv` and
`SubgroupFunctor.IsRepresentedBy.isoOfComap`. Its provenance is the explicit
algebra calculation and the full represented-subgroup comparison above.
