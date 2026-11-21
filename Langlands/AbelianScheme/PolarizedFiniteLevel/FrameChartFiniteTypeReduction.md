# Finite type of frame charts from the locally closed Hilbert locus

`frameChartFiniteType_of_frameHilbertLocus` derives the published
`FrameChartFiniteTypeStatement` from the frame Hilbert locus,
determination of the polarization by the cubic bundle, isomorphism
invariance of the frame locus, and existence and uniqueness of frame
embeddings. The published frame-locus base change is used as a theorem.
The reduction works for every level `n ≥ 3`, so it takes the eventual
bound to be `3`.

The proof uses the classifying family for the fixed cubic Hilbert
polynomial, rather than the family for all Hilbert polynomials. The
frame Hilbert locus gives an immersion into that finite-type ambient
base and a datum on the locus. An immersion is locally of finite type
and induces the subspace topology. The noetherian ambient topology
therefore gives a compact source. Composing the immersion with the
structure map of the ambient base gives a locally finite-type map to
`Spec (ULift ℤ)`. By terminality it is also the composite through
`X.toLocalizationSpec`, so `locallyOfFiniteType_of_comp` applies.
Compactness of the source gives quasi-compactness of this map to the
affine localization base.

The datum is universal for its frame chart. Its pullbacks retain frame
locus `⊤`; an isomorphism between two pullbacks identifies their embedded
ideals and indexed points using uniqueness of the frame embedding.
Uniqueness of the classifying map, followed by cancellation of the
immersion, identifies the two base maps. Conversely, any datum whose
frame locus is `⊤` has an embedding and a classifying map. The latter
factors through the frame Hilbert locus, and equality of realized
families recovers the isomorphism with the universal pullback. The
published `frameChart_of_isUniversalFrameDatum` gives the required
natural transformation and identifies its image.

This is an internal reduction: it adapts the published frame-chart
representability argument to the fixed-polynomial ambient family in
the Hilbert-locus setup of Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, 3rd ed., pp. 131–138. It does not prove the locally closed locus
statement or the other listed inputs.
