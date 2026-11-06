# The compact open norm kernel of the actual centralizer

This internal derived construction applies to every supplied
`ValuationBuildingData G`, at every universe `u`, over a nonarchimedean local
field of either characteristic. It proves connected reductivity of the actual
centralizer, compactness and openness of its actual common rational character
norm kernel, and algebraic boundedness of that kernel's image in the original
ambient group. It assumes no apartment axioms, anisotropy, splitness of the
centralizer, or unproved structural statement.

The centralizer is exactly `B.centralizer.Z`, with its supplied closed inclusion
`B.centralizer.j` representing the whole all-test centralizer of `B.i`.
`isConnectedReductive_centralizer` applies the published
`dynamicCentralizerReductive` through
`IsSplitTorus.isConnectedReductive_centralizer_of_dynamic`. The latter chooses
a cocharacter of the actual split torus whose centralizer is the whole torus
centralizer. The ambient connected reductivity is a field of the supplied
building datum. No torus presentation of the centralizer is asserted.

`centralizer_isCentral_maximalSplit` proves that the supplied map
`B.centralizer.s` is central and maximal split in this same centralizer.
Represented centralization and the equality `s ≫ j = B.i` prove centrality.
Closedness of `j` transfers maximal splitness from `B.i`. This extends the
existing parahoric-data lemma to valuation-building data, which needs no
derived covers or zero-subgroup choices.

`isCompact_centralizerNormKernel_of_valuationData` then applies the existing
`isCompact_rationalCommonNormKernel_of_central_maximalSplit`, discharging its
two whole-statement premises with the published `centralQuotientReductive`
and `anisotropicCompactness_proof`. That adapter constructs the actual smooth
anisotropic quotient by the central maximal split torus and applies the
published central-split quotient compactness argument. Thus it proves
compactness of the norm kernel in the full centralizer point group, with
exactly `rationalPointTopology F B.centralizer.Z.X`. Affineness is derived
from the actual closed inclusion.

`isAlgebraicallyBounded_image_centralizerNormKernel` uses the existing
compact-to-algebraically-bounded theorem and boundedness under the actual
rational-point map. `isOpen_centralizerNormKernel` uses the published openness
of the common norm kernel, with local finite type supplied by the just-proved
smoothness of the centralizer. `centralizerNormKernelData` packages this same
kernel as an open subgroup, with an equality of underlying subgroups,
compactness, and algebraic boundedness of its image under `B.centralizer.j`.

The provenance is the assembly of these published group-scheme and
rational-point theorems; no new independent literature assertion is made.
The result concerns the norm kernel, not compactness of the entire centralizer
point group. It does not construct general valuation-building data, prove
openness of the actual centralizer-zero subgroup, or prove the unrestricted
root-valuation building construction statement.

The central and maximal split factor lemma is reused from
`SharpFixerBoundednessStructuralReduction`. Its earlier conditional compactness
theorem retains its original name and hypotheses.
