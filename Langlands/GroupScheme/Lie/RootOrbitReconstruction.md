# Reconstruction of actual root-orbit vectors from their components

This internal construction sums actual Lie-root vectors into their literal
ambient Lie module. For an internal submodule decomposition and an injective
finite collection of its indices, `finiteWeightSumEquiv` identifies dependent
tuples of component vectors with the supremum of those actual submodules.
Projection onto a chosen component recovers that component of the finite sum.
Conversely, submodule-supremum induction proves that a vector in this span is
the sum of its component projections.

`rootOrbitWeightSpan` is the supremum of the actual adjoint root weight spaces
over one ordinary Galois orbit of actual roots, inside the Lie kernel of the
actual scheme base change. `rootOrbitSumEquiv` is the resulting linear
equivalence from all dependent root-vector tuples to that ambient submodule.
It assumes an affine locally finite-type ambient group, a finite extension,
and that the base-changed acting torus is split. No reductivity, maximality,
dimension-one or Galois extension hypothesis is needed for this sum
equivalence.

The provenance is internal: the construction uses the published actual
split-torus weight decomposition and its component projections. It does not
yet restrict this sum to invariant tuples, identify a whole relative-root
restriction fiber with a single orbit, or give actual root-field coordinates
or apartments.
