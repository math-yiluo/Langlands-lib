# Actual module maps from natural linear free-section transformations

This internal prerequisite for the relative radical quotient descent reconstructs an actual module-sheaf morphism from a natural linear
transformation on free coordinate sections over every scheme test, with an
arbitrary fixed target module. The original global generator images are recovered
from the identity test using the canonical module identity-pullback comparison.
They construct an actual map by the free-sheaf universal property. Naturality
and linearity recover the prescribed transformation on every test in canonical
free section coordinates.

This is intended for each disjoint source-component inverse image in the actual
quotient overlap descent, where the source module is free and the target module
may have varying ranks. The actual quotient transition linearity and subsequent
gluing/cocycle still must be supplied by the parent construction.

The target module need not be free or quasi-coherent, and no finite-rank
condition on it is imposed. The source rank may be zero, and the scheme base
may be arbitrary or empty. `pullbackSection_identity` and
`sectionPullback_toIdentity` verify the exact canonical identity-comparison
normalization used to extract the generator images.

`images_pullback` applies the original transformation's naturality to the
actual map from a test to the identity test. Each original coordinate vector
pulls back to the same coordinate vector. The actual free-sheaf map then has
the prescribed action on every canonical pulled-back basis.
`moduleHom_coordinates` uses finite free coordinate expansion and the supplied
linearity to prove the complete all-test action, without a sheaf-map
effectivity premise.

Provenance: an internal derivation from the free-sheaf universal property,
the canonical identity and composition comparisons, and the supplied natural
linear transformation.

The map `toIdentity` uses `LocalGroupIso.terminalBasePoint` on each test.
