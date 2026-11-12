# Closed subgroup embeddings of norm-one rational quotients

Author: Worker 82.

`AdelicGroupPoints.normOneRationalQuotientMap F G H f` is the actual map
`G(F) \ G(𝔸_F)¹ → H(F) \ H(𝔸_F)¹` induced by the published continuous
`mapNormOne F G H f`. Naturality for principal points makes it descend to left
cosets. `normOneRationalQuotientMap_mk` gives its representative formula, and
`continuous_normOneRationalQuotientMap` proves continuity by the quotient
universal property.

`NormOneRationalQuotientClosedImmersionStatement` is a proposition target,
not a theorem. It asserts that this map is a closed topological embedding
for a closed immersion of affine group schemes locally of finite type over
an arbitrary number field in universe `u`. It does not require reductivity,
connectedness, normality, supplied quotient compactness, or an adapted
representation. It is Springer's Lemma 1.3, expressed on the Library's actual
carriers and topologies. Springer writes rational cosets on the right;
inversion exchanges this convention with the Library's left cosets.

The helper theorem `LeftCosetSpace.exists_isCompact_representatives` constructs
a compact set of representatives whenever a locally compact topological group
has compact left quotient by a subgroup. Choose a compact neighborhood of every
group element. The images of their interiors under the open quotient projection
cover the quotient. Compactness selects a finite subcover; the corresponding
finite union of compact neighborhoods meets every coset. Equality of quotient
classes supplies the left subgroup translate. No normality or discreteness
assumption is used.

For actual finite-type affine groups,
`hasCompactNormOneRationalCover_iff_compactSpace` combines that construction
with the forward implication in `AdelicNormOneCompactCover`. Thus the compact
cover formulation can be recovered from a proof of quotient compactness.
The theorem `hasCompactNormOneRationalCover_of_isClosedEmbedding` further
recovers the cover when any closed embedding of the actual quotient has
relatively compact image. The inverse image of the compact closure of the
range is the entire source quotient, hence is compact, and the preceding
construction applies. These are conditional topological tools, not a proof
of either the closed-immersion statement or the central-split compactness
theorem.

Source: T. A. Springer, *Reduction theory over global fields* (1994), §1.3,
printed p.208 (PDF p.2). The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
`literature/Reduction theory over global fields (Springer, 1994).pdf`.
Springer proves closedness using a representation adapted to the subgroup
from §1.2 and norm-one idele compactness. This module does not implement
that argument; the helper topological proofs are internal derivations.
No errata note exists for this source.
