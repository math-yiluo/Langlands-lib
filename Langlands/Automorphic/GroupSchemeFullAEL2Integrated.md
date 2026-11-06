# Bochner integration on the original full AE cuspidal L2 space

This internal adapter integrates the original full almost-everywhere
cuspidal representation inside its original complete submodule of the
canonical positive-central quotient L2 space. The submodule still imposes
separate almost-everywhere absolute convergence and vanishing of periods
for every actual proper rational parabolic. Its carrier, quotient measure,
null classes and inherited norm are unchanged.

`fullAEL2CuspidalBoundedRightAction` uses the bounded linear maps of the
original invertible right isometries. Its identity and multiplication laws
reduce through the subtype inclusion to those of the original ambient
action. Continuous original cusp orbits are strongly measurable for any
specified measure `ν` on the actual adelic group, using that group's
existing second-countable Borel topology. No separability assumption on
the cusp Hilbert space is needed.

For a supplied complex function `f` with `Integrable f ν`, the public
`integratedIsometricAction` constructor first proves Bochner
integrability of every weighted orbit `a ↦ f a • ρc a φ` using the
integrable scalar majorant `‖f a‖ * ‖φ‖`. The resulting
`fullAEL2CuspidalIntegratedAction` is an actual bounded complex-linear
endomorphism of the original cusp carrier. Its value is definitionally
that orbit integral, and its operator norm is at most `∫ a, ‖f a‖ ∂ν`.
Completeness is supplied by the actual all-parabolic closedness theorem
in `GroupSchemeFullAEL2Hilbert`, rather than a new closedness premise.

The faithful original inclusion is an isometry and commutes with Bochner
integration. Hence `fullAEL2CuspidalIntegratedAction_val` identifies this
operator exactly with the ambient `haarQuotientL2IntegratedAction` on
the included vector. This proves ambient invariance of the original full
cusp submodule under every such integrated operator.

The original subtype-valued orthogonal projection also commutes with
these integrals: absolute integrability is proved by the ambient adapter,
the continuous linear projection can therefore pass through the Bochner
integral, and the original projection equivariance identifies the
integrands. Passing through the faithful inclusion gives the corresponding
commutation identity for the original ambient orthogonal cusp projection.
These are equalities of actual L2 vectors, with no pointwise
identification of their chosen measurable representatives.

All original number-field, affine locally finite-type group, connected
reductive, parabolic-dynamic, supplied central split-torus, finite
splitting, injective finite-index character-restriction and norm-one
right-Haar hypotheses remain explicit. The group integration measure
is arbitrary and independent of the unchanged canonical quotient measure;
it may in particular be specialized to inverse group Haar for the right
Haar convention. No convolution identity, smoothness, density,
compactness, trace or spectral decomposition is asserted.

Provenance is internal: the construction composes the original full
cusp Hilbert, action and continuity adapters with the published
Bochner integrated-operator API and pinned Mathlib integration through
linear isometries and continuous linear maps. It claims no additional
result from external literature. Its original Hilbert, continuity and
ambient integration dependencies are published Library constructions.
