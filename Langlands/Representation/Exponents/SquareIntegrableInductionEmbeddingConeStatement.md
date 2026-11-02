# Strict scalar cones from actual normalized induction embeddings

`Langlands.SquareIntegrableInductionEmbeddingConeStatement` is an internal
prerequisite for the analytic segment classification. It quantifies over every
prime, supplied p-adic field and topological datum, with independent field and
carrier universes and carriers in `Type (max uF uV)`.

Let `π` be an actual nonzero smooth complex representation of `GL_n(F)`, with
`n > 0`, that is analytically square-integrable. Let `B` be any standard block
shape and `σ` an actual smooth representation of its Levi. Suppose that `π`
embeds by an injective intertwiner into the normalized upper parabolic
induction of `σ`. Suppose also that the block-scalar split centre acts on all
of `σ` by a supplied character `χ`. Every supplied real-part vector `x` of
`χ` then has total sum zero and strictly positive proper initial sums.
Coordinates are scalar coordinates, so any degree weighting in determinant
coordinates is already included in `x`.

The functors are the existing actual functors: upper block parabolics, positive
half-modulus in induction, inverse half-modulus in Jacquet modules and right
translation. Neither irreducibility nor finite length is assumed for `π` or
`σ`. Nontriviality of `π` is explicit; analytic square-integrability alone does
not serve as a nonzero certificate.

The internal derivation uses normalized first adjointness and
`Langlands.squareIntegrableActualJacquetCone`. An embedding from nonzero `π`
is nonzero, so its adjoint Jacquet map is nonzero. Its actual invariant image
is a nonzero quotient of the whole normalized Jacquet module. Scalar action
on `σ` restricts to this image. The published scalar Jacquet-subquotient
theorem therefore supplies the stated cone. No assertion that the whole
inducing representation is a Jacquet quotient is needed.

This file defines a proposition, without proving it. It neither provides the
induction embedding nor constructs a scalar character or a real-part vector.
It does not assert segment commutation or either direction of analytic segment
classification. The provenance is this internal consequence of the published
adjunction and scalar Jacquet-cone interfaces; no new original literature is
invoked.
