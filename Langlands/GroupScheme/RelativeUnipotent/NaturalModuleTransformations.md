# Natural linear transformations of actual module sections

This internal Task 7200 adapter works with arbitrary module sheaves on an
arbitrary scheme at universe `u`. A `Transformation M N` is a linear map on
the global sections of the actual pullbacks of `M` and `N` to every scheme
test, natural for the canonical relative section pullbacks.

An actual module morphism defines such a transformation. Composition uses the
original section maps. Arbitrary base change uses the prescribed canonical
pullback-composition isomorphisms, whose existing section naturality proves
the new transformation's naturality.

For a finite free source, `freeCoordinates` uses the canonical actual
pullback basis to give the previously constructed source-free reconstruction
interface. `reconstructFree` therefore constructs an actual module-sheaf
morphism. `reconstructFree_apply` proves that its actual pullback action equals
the original transformation on every section of every test, without a
condition on the target module.

The provenance is derived from actual module pullback coherence, section
naturality, the canonical free bases and source-free section reconstruction.
The module provides infrastructure for reconstructing the original radical
quotient overlap maps; it does not assert a compatible overlap cocycle or the
final radical-filtration statement.
