# Continuous projectors for actual archimedean compact types

Author: Worker 94.

This internal proof assembles character averaging on the actual compact
subgroup `standardInfiniteCompact K n`. Equip the subgroup with its Borel
sigma algebra and choose Haar measure normalized on the whole compact group.
This is a left invariant probability measure. Right translation preserves
left invariance and total mass; uniqueness of Haar measure on a compact group
therefore proves right invariance.

For each actual compact type, choose the continuous operator given by its
degree times its inverse character. The matrix-coefficient intertwiner
construction places every value in the published algebraic isotypic span.
Finite-dimensional Schur conjugation averaging, applied to coordinate rank-one
endomorphisms, proves source-character reproduction. Scalar evaluation passes
that identity through every algebraic intertwiner into smooth functions, and
finite sums give fixation on the entire compact-type submodule. Cyclic
invariance of trace and bi-invariance of the measure give compact equivariance.
The weighted-average construction supplies containment in the closed complex
span of the actual compact orbit.

Thus `Langlands.Global.ArchimedeanGL.compactTypeProjection` proves exactly
`CompactTypeProjectionStatement K n`, for arbitrary number-field universe and
every natural rank, including zero. The proof integrates scalar evaluations
and finite-dimensional source vectors; it does not require completeness of
the full derivative smooth-function space.

The motivating character projector is described in Harish-Chandra,
*Discrete series for semisimple Lie groups II*, section 2, printed/PDF page 8
(registered source `harish-chandra-1966-discrete-series-ii`). The explicit
scalar construction, algebraic isotypic range and closed-orbit containment
are internal developments. The theorem proves the published statement; independent semantic review
and publication of this proof are separate steps. It does not establish admissibility,
analyticity, convolution reproduction or automorphic differential growth.
