# Finite central coverings of actual generated compact types

Author: Worker 94.

`Langlands.Global.ArchimedeanGL.compactTypeCentralSpan` proves exactly the
published `CompactTypeCentralSpanStatement K n`. The number field `K` is
in arbitrary universe and `n` is any natural number, including zero. The
statement and its imports are unchanged.

The inclusion of the generated module is the actual subtype inclusion and
intertwines the entire compact group. Its range is the exact complex span in
`CompactTypeCentralSpanStatement`. Applying algebraic isotypic restriction
with the compact type's given irreducibility identifies the image of the
internal isotypic part with the required ambient compact-type intersection.

The proved `exists_finite_central_cover_generatedModule_isotypic` supplies a
finite family of linear maps from the compact type's finite coordinate space
into the genuine generated enveloping module. The central spans of their
basis evaluations cover the internal isotypic part. Applying the inclusion
to this containment preserves the supremum of submodules. The lemma
`generatedModule_centerOrbit_map` identifies each resulting span with the
published full center orbit of the corresponding actual smooth function,
transported back by `toSmooth.symm`. This follows by mapping the spans of
the orbit ranges: both actual center actions agree through the inclusion
and the smooth-function equivalence.

The evaluations are indexed by `Fin m × Fin σ.dim`. The proof uses
`finProdFinEquiv` to obtain exactly the required family indexed by
`Fin (m * σ.dim)`. Each vector belongs to the published generated complex
span by the proved restriction-of-scalars identity. The isotypic image
comparison and the mapped central covering then give the target inclusion.

The covering uses full center orbits of vectors in the generated module.
It asserts containment and requires neither that these vectors lie in the
selected compact type nor that center orbits be finite-dimensional. No
center-finiteness hypothesis or connectedness assumption is added.

The construction is derived from the actual generated-module and finite-source
results and the algebraic injective isotypic restriction theorem. It retains
the whole standard compact group. These internal algebraic constructions are
the provenance of this proof; it does not claim a direct translation of a
literature theorem. Finite multiplicity after center finiteness, analytic
density and closure, convolution reproduction and automorphic differential
growth remain separate obligations.
