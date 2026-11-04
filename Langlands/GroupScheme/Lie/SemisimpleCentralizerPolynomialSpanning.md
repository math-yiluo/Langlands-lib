# Polynomial criteria for actual semisimple-centralizer spanning

`Lie.noncentralSemisimpleCentralizerSpan G` is the supremum of the actual
tangent submodules `elementCentralizerLie G X` for ground-field tangent
elements `X` which are representation-semisimple and have proper tangent
centralizer. It is a submodule of the actual additive dual-number identity
kernel. These are exactly the submodules in the spanning conclusion of
`Lie.SemisimpleCentralizerSpanningStatement`.

The first criterion uses any finite basis `b` of this actual Lie module over
an infinite field and any nonzero polynomial `p` in those coordinates.
Its explicit hypothesis says that for every ground-field vector `x` at which
`p` is nonzero, there is a noncentral representation-semisimple vector `Y`
whose actual tangent centralizer contains `x`. It concludes that such a `Y`
exists over the ground field and that the supremum above is the whole
Lie module.

The implemented proof uses the paired helper
`Langlands.LinearAlgebra.PolynomialNonvanishingSpan`. Its nonvanishing
existence lemma provides a vector to which the hypothesis applies.
Its subspace criterion shows that any submodule containing the nonvanishing
locus is the whole module. The defining supremum contains each of the
centralizer submodules, so the hypothesis puts that locus in the supremum.

For affine locally finite type groups, the second criterion replaces the
membership hypothesis by `Y ∈ elementCentralizerLie G x`. The imported
`mem_elementCentralizerLie_comm` gives exactly the reverse membership needed
by the first criterion. The first criterion itself needs affineness but
neither finite type, smoothness nor connectedness. The field and finite
basis index have independent universes, and no characteristic, perfection,
splitness or positive-dimension restriction is used.

This is a derived internal construction and reduction, using the published
actual tangent-centralizer and semisimplicity definitions and the polynomial
helper included in this unit. It does not construct the polynomial or prove
the centralizing semisimple replacement hypothesis from a geometric
semisimple element. Those obligations, and therefore the complete spanning
statement and Cartan-generation theorem, remain open.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
