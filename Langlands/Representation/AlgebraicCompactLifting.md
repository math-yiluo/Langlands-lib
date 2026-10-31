# Bounded invariant preimages from source averaging

This internal argument extends the existing algebraic compact average. The
source representation has finite dimensional continuous orbit spans on a
compact Borel group, so its algebraic finite-span integral is defined. The
measure is finite; the constant-image and preimage results additionally require
probability normalization, and fixedness of the averaged source vector requires
left invariance and measurable multiplication.

`average_mem_submodule` proves that every complex submodule containing all
points of a source orbit contains its average. Apply the quotient map by the
submodule and then an arbitrary algebraic dual functional. The scalar integrand
is zero, so dual separation in the quotient proves the assertion. No topology or
closedness of the submodule is assumed.

`map_average_eq_of_orbit_constant` considers a complex linear map into an
arbitrary complex vector space. If that map is constant on a particular source
orbit, its value on the source average is the same constant. Composing with each
target algebraic dual functional reduces the assertion to the scalar integral
of a constant under a probability measure.

For `exists_invariant_preimage_mem`, the target has any algebraic group
representation and the linear map is equivariant. A fixed target vector with a
preimage in a stable source submodule is lifted by averaging that preimage.
The first lemma retains membership in the chosen source submodule, left Haar
invariance gives a fixed source vector, and equivariance plus target fixedness
make its image constant on the source orbit. The second lemma therefore
identifies the image of its average with the original target vector.

The proof integrates only the source orbit. There is no topology or finite
continuous orbit assumption on the target. These are internal consequences of
the published finite-span integral, algebraic dual separation and compact
average, and make no claim about finite generation or automorphic growth.
