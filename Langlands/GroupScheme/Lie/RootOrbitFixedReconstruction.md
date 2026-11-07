# Invariant root tuples and actual fixed ambient Lie vectors

This internal construction restricts the actual finite root-orbit sum to
Galois invariants. The carrier `rootOrbitFixedSpan` consists of vectors in
the actual ambient root-orbit weight span fixed by every canonical semilinear
Galois map on the actual scheme base change. Its definition does not assume
that the field extension is finite or Galois.

The generic lemma `finiteWeightSum_fixed_iff` applies to a finite injective
family in an internal submodule decomposition and an additive group action
permuting these actual components. Invariant tuples have fixed sums by
reindexing. Conversely, transport a tuple by an element of the group and
reindex by its inverse. Fixedness of the total sum says that the transported
tuple has the same sum; injectivity of the published finite sum equivalence
then recovers the componentwise invariance condition. Semilinearity is not
needed for this argument.

The actual canonical Galois maps preserve the corresponding actual adjoint
weight spaces with their transported characters. Specializing the generic
lemma therefore identifies invariant actual root tuples with precisely the
fixed vectors in their literal ambient span. This is the additive equivalence
`rootOrbitInvariantSumEquiv`. It assumes an affine locally finite-type ambient
group, a finite extension and splitness of the base-changed acting torus.

For a connected reductive group and an original maximal torus, and when the
finite extension is Galois, `rootOrbitFieldFixedSpanEquiv` composes this sum
with the constructed coherent root-line coordinates and orbit-field
parametrization. Its domain is the actual root-stabilizer fixed field. It is
an additive equivalence with actual fixed ambient Lie vectors, rather than
only a tuple model. These constructions work in every characteristic and
common universe.

The provenance is internal, using the actual split-torus weight decomposition,
canonical Galois weight transport, effective Lie descent's fixed carrier and
the published coherent root-orbit coordinates. No equality of a relative-root
restriction fiber with a single Galois orbit is claimed here. Identifying these
fixed vectors with an entire original relative weight space, constructing the
root-field character and actual rational root-point coordinates, and apartment
existence remain separate obligations.
