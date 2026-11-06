# From common induction embeddings to an actual nonzero unitary piece map

This derived supporting construction implements the passage from common
induction embeddings to a nonzero unitary geometric-piece map in Renard,
*Représentations des groupes réductifs p-adiques*, edition dated 9 July
2026, VII.2.6 theorem, uniqueness proof, printed p.231 / PDF p.237.

The two original representations `σ` and `τ` belong to the rational
Levis `M` and `L` of actual rational parabolics of `G`. An irreducible
smooth representation `π` has specified injective intertwiners into
their actual normalized inductions `I₁` and `I₂`. Semisimplicity of
`I₁`, normalized-exponent temperedness of `I₁`, and normalized-exponent
temperedness of `τ` are explicit additional inputs to this supporting
construction. A split component of `L` specifies the unitary Jacquet
module along the second parabolic.

`nonzeroUnitaryJacquetMapOfInductionEmbeddings` first derives
nontriviality of the original carrier of `π` from irreducibility.
Consequently, its second injective intertwiner is nonzero. The
published `nonzeroSemisimpleIntertwiningExtension` extends that map
across the first embedding to a nonzero intertwiner `I₁ → I₂`.
The extension uses an actual equivariant retraction supplied by
semisimplicity of `I₁`. Applying the published tempered Frobenius
reciprocity linear equivalence gives an actual nonzero intertwiner
`(r_Q I₁)₀ → τ`. The equivalence preserves zero and is injective, which
proves nonzeroness of its image.

This route extends the original map before applying reciprocity. In
Renard's proof, one first regards `π` as a quotient of `I₁` and applies
exactness of the Jacquet functor. The implemented route has the same
output and avoids requiring a separate quotient-map comparison.

`nonzeroUnitaryPieceMapOfInductionEmbeddings` additionally consumes a
specified actual finite filtration of `(r_Q I₁)₀`, a permutation of the
intersection indices, and representation equivalences from its graded
pieces to the published `unitaryPieceRep` objects. It applies
`nonzeroUnitaryPieceMapOfFiltration` to the preceding nonzero map. The
output records a selected intersection index and an actual nonzero
intertwiner from that unitary geometric piece to `τ`.

The field universe `u` and all three original carrier universes `v`,
`w`, and `x` remain independent. The actual normalized functors and
canonical point topologies are unchanged. No standardness of either
parabolic is assumed.

The filtration and its graded equivalences are supplied rather than
constructed. This file proves neither VII.2.5 nor semisimplicity or
temperedness of an induced representation. Square-integrability and
fullness of the intersection parabolics are not conclusions here.
The final conjugacy argument and all three exact VII.2.6 propositions
remain separate obligations.
