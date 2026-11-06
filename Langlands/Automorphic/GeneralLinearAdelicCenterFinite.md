# General-linear comparison of whole-function center finiteness

This internal construction compares the existing general group-scheme and
matrix general-linear center-finite spaces over an arbitrary number field in
universe `u`, at every natural rank, including zero. A proof of smooth relative
dimension for the actual general-linear group scheme supplies the same atlas
used in the preceding differential comparisons. No reductivity, matrix-embedding,
maximal-compact, growth or tensor hypothesis is required for this comparison.

The construction directly reuses the existing
`GeneralLinearGroupPoints.infiniteCenterEquiv` with the adelic algebra
abbreviation. It identifies the actual associative centers of the
complex identity-tangent and original matrix enveloping algebras. The theorem
`finitePlotSmoothGeneralLinearEquiv_adelicCenterAction` reuses the published
whole-function center-action comparison. It retains the unchanged linear
equivalence between original finite plot-smooth rational functions and original
matrix finite-smooth rational functions.

`generalLinearAdelicCenterIntertwiner` bundles that original function map as
an intertwiner, with the matrix action pulled back along the center equivalence.
An injective intertwiner preserves and reflects finite orbit spans. Surjectivity
of the center equivalence then identifies the reindexed orbit with the entire
matrix-center orbit. The published faithful extraction of all finite slices
identifies the latter with the original `IsCenterFinite` condition. This proves
`isAdelicCenterFinite_iff_generalLinear`. Both sides impose one finite-dimensional
orbit of the whole function, equivalently of the entire family of slices;
there are no slice-dependent finite-dimensional bounds.

`generalLinearAdelicCenterAnnihilator` proves equality of the actual global
annihilator ideal with the pullback, along this same center equivalence, of the
original common slice-family annihilator. Its proof uses the center-action
identity and joint injectivity of all original finite slices. Conversely,
annihilation of the entire actual function gives annihilation on every matrix
slice. This equality holds for every finite-smooth function, whether or not
its center orbit is finite.

`finitePlotSmoothGeneralLinearCenterEquiv` restricts the original function
linear equivalence to the two existing global center-finite submodules.
Its value theorem is reflexive: the original function map is unchanged.
The inverse uses the proved finiteness equivalence and the original inverse
laws.

The intermediate declarations retain the earlier scalar-commutator proof
parameter. It adds no hypothesis to the actual comparison:
`adelicDifferentialCommutator_of_smooth` already proves it on this atlas, and
`isActualAdelicCenterFinite_iff_generalLinear` explicitly supplies that theorem.
Proof irrelevance identifies all choices of this proof.

The provenance is internal: the construction uses the published actual
center and function equivalences, finite-vector injection theorem, faithful
matrix slice-family comparison and actual scalar-calculus theorem. It asserts
no growth equivalence, tensor-rank implication, automorphic-form equivalence,
cuspidal comparison, quotient-measure theorem or reduction result. The general
form growth condition ranges over all adeles, while the older matrix form
condition uses archimedean slice growth; their comparison remains separate.
