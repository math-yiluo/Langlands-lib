# Unions of represented open charts

This derived helper implements the finite open-union step used in the proof
of Stacks Project Lemma 67.50.1 (Tag 03XW), in the registered source
`stacks-03XW-2026-11-02`, `03XW.html:209-215`. It uses the already published
`SliceOpenGluing` construction for schemes over the original base.

For a family of scheme maps into an arbitrary presheaf, `union` is the fppf
local closure of the union of their ranges. The equality
`union_eq_sheafify_iSup` identifies this definition with the local closure of
the pointwise supremum of the ranges. The construction uses the range of the
coproduct map, without claiming that a coproduct of representable presheaves
is itself represented by the scheme coproduct.

`chart` is each chart's canonical factorization into this local union.
Its square with the union inclusion is cartesian because the inclusion is a
monomorphism. Hence an open chart remains an open immersion into the local
union. The resulting family is locally surjective by the definition of local
closure. If the ambient presheaf is an fppf sheaf, the local union is also an
fppf sheaf.

`scheme` is the actual scheme over the same base obtained by gluing these
charts along their represented overlaps. `iso` proves that it represents the
local union. If the index type is finite and each chart scheme is compact,
`scheme_compactSpace` proves compactness of this representer using its actual
finite open cover. Thus the result applies to the two compact charts in the
diagonal and off-diagonal induction step.

The base and all scheme charts have arbitrary universe `u`; the index type
is in that same universe. No separatedness, affineness, or representability
assumption on the ambient presheaf is used. This file does not establish
descent effectivity or the final algebraic-space schemehood statement.
