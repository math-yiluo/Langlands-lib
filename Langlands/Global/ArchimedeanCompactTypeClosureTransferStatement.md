# Closure transfer for actual compact-type intersections

Author: Worker 94.

`Langlands.Global.ArchimedeanGL.CompactTypeClosureTransferStatement K n`
is an internal topological prerequisite for the differential-growth argument.
It uses the published actual compact subgroup, its representation on
`DerivativeSmoothFunctions K n`, the full derivative topology and the algebraic
isotypic submodule `compactTypeSubmodule σ`. Its number-field universe and
natural rank are arbitrary, including rank zero.

For a complex submodule `M`, assume invariance under every actual compact
translation and compact finiteness of every vector in `M`. For each actual
compact type `σ`, additionally assume that `M ⊓ compactTypeSubmodule σ`
is finite-dimensional. The statement says that

`M.topologicalClosure ⊓ compactTypeSubmodule σ = M ⊓ compactTypeSubmodule σ`.

Thus closure introduces no new vectors of this selected compact type. The
finiteness hypothesis concerns the selected algebraic intersection; it does
not assert finite dimension of the whole isotypic submodule, of `M`, or of
its closure. No completeness of the smooth-function carrier is assumed.

The provenance is internal topological linear algebra. The intended proof
uses the continuous actual compact-type projectors specified by the published
`CompactTypeProjectionStatement`. A projector value lies in the closed span
of the input's compact orbit. For an input in `M`, that orbit span is
finite-dimensional, closed and contained in `M`, so the projector preserves
`M`. The inverse image of the finite-dimensional intersection under the
continuous projector is closed and contains `M`; it therefore contains its
closure. Fixation on the type proves the asserted equality. These are proof
obligations, rather than hypotheses or conclusions supplied by this module.

Only a proposition is defined here. The projector construction and proof of
this statement require independent proof review and publication. Algebraic
finite multiplicity, density of the compact-and-enveloping orbit, convolution
reproduction and automorphic differential growth remain separate obligations.
