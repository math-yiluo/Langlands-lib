# Finite central orbit coverings of actual compact fixed vectors

This internal derived result concerns a genuine complex module for the actual
archimedean enveloping algebra and a compatible representation of the full
standard compact subgroup. A finite continuous compact representation maps
equivariantly into that module, and its image is stable under the actual compact
Lie generators. The target module needs no topology or orbit finiteness.

For any finite homogeneous generating family of the actual Cartan covariants,
`cartanCovariantCentralSpan` is the sum of the complex spans of the full center
orbits of the images of those generators under the actual Cartan tensor action.
The finite family is independent of the enveloping filtration degree.

The construction is derived internally from the published actual Cartan tensor
action, invariant tensor lifting, homogeneous covariant generators and strict
filtered action comparison. It does not identify this intermediate claim with a
literature theorem. The proof uses exact homogeneous invariant coefficients for
each homogeneous covariant. Their actual symmetrizations are central and fixed by the whole
archimedean group. Compatibility of the compact and enveloping actions therefore
makes their actions on fixed vectors fixed. The sum of those central actions is
in the finite central covering. Its difference from the original tensor action
image lies in the action span of one lower enveloping degree: the coefficients
have the exact complementary degrees, and coefficients of excessive generator
degree are zero. At degree zero, the scalar comparison gives exact equality.

Strong induction on the enveloping degree completes the fixed-vector assertion.
A fixed vector has a fixed tensor preimage with the same bound, which decomposes
into fixed homogeneous components through that bound. Apply the homogeneous
argument to each component. Its error is fixed and has strictly lower degree,
so the induction hypothesis covers the error and hence the original component.
Exhaustiveness and monotonicity of the actual enveloping filtration extend the
covering to its entire generated action span.

`fixed_mem_cartanCovariantCentralSpan_of_mem_envelopingDegree` gives the bounded
assertion, and `fixed_mem_cartanCovariantCentralSpan` gives the exhaustive one.
`exists_finite_central_orbit_cover_of_compact_fixed` finally uses the proved
existence of finite homogeneous covariant generators to supply
the finite family without a generator-family hypothesis. All conclusions retain
arbitrary number-field universe, arbitrary target universe, and all natural
ranks. This covers the fixed subspace only. Application to arbitrary compact
types still requires a tensor-dual comparison and an actual finite compact
source, and the automorphic differential growth theorem remains open.
