# Compact rational covers of actual norm-one adelic points

Author: Worker 82.

This module defines `AdelicGroupPoints.HasCompactNormOneRationalCover G`: a compact
subset of the existing `normOneSubgroup F G` meets every principal rational left
coset. Its carriers, rational map and topology are those of the Library. It also
proves compactness of `NormOneRationalQuotient F G` from this property, transport
along a group-scheme map surjective on norm-one points, invariance under actual
group-scheme isomorphisms, and the property for every actual split torus, including
rank zero and `Gm`.

The definition is an internal abbreviation of the compact-representative conclusion
of `AdelicSiegelFactors.CentralSplitCompactQuotientStatement`. It assumes no
reductivity or torus structure. The transport lemmas follow from continuity and
naturality of the published `AdelicGroupPoints.mapNormOne`. To obtain quotient
compactness, map the compact representative set through the continuous left-coset
projection; principal multiplication preserves its image and proves surjectivity.

For the split torus with finite index type `I`, take the finite product of the
compact norm-one idele representative set constructed in
`NormOneIdeleClass.exists_isCompact_fundamentalSet`. Pull it back through the
published `splitTorus.affinePointsHomeomorph`, and intersect with norm-one points
by taking the inverse image under their closed subtype embedding. Each coordinate
of a norm-one torus point is a norm-one idele: apply the definition to the
corresponding projection character. Reduce these coordinates independently by
principal ideles. The rational split-torus point with those coordinate units
acts by the chosen principal ideles, by `character_rational`. The translate
therefore belongs to the compact set. An arbitrary `IsSplitTorus` is handled by
its actual group-scheme isomorphism and the transport lemma. The `Gm` result
uses the published rank-one isomorphism.

This is a derived special case of T. A. Springer, *Reduction theory over global
fields* (1994), §1.7, printed p.209, which reduces split-torus compactness to the
multiplicative group. The implemented proof uses the Library's proved norm-one
idele compact representatives directly. The source is registered as
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, file
`literature/Reduction theory over global fields (Springer, 1994).pdf`, PDF p.3.
There is no errata note for this source.

This module does not prove compactness for nonsplit tori or anisotropic
semisimple groups, and does not prove `CentralSplitCompactQuotientStatement`.
