# Actual analytic data for the parabolic orbit integral

This internal prerequisite supplies analytic inputs for the actual nested
kernel of `parabolicOrbitStagesRetraction` and its actual stabilizer
intersection. It does not construct the final orbit comparison.

`parabolicOrbitNestedRadicalEquiv` removes the intermediate stages subtype
using the published continuous kernel equivalence. The resulting group is
the intrinsic target block radical, with its supplied subspace topology.
The nested intersection is closed because the actual orbit stabilizer is
closed and both intervening subtype inclusions are continuous.

For every prime, actual finite p-adic extension and supplied compatible
topology, `parabolicOrbitNestedKernel_compactOpenCover` applies published
finite compact containment to the singleton consisting of the image of a
kernel element. Pulling the resulting compact open subgroup back along the
continuous group equivalence gives a compact open subgroup containing that
element. `parabolicOrbitNestedKernel_compactOpenBasis` similarly pulls back
the published actual radical compact open neighborhood basis.
`parabolicOrbitParabolic_compactOpenBasis` specializes the published actual
parabolic basis. These results allow every rank and permutation.

`parabolicOrbitNested_measureExists` uses the canonical Borel measurable
structures on the actual kernel, intersection and left quotient. Local
compactness of the kernel is transported from the actual radical, and
closedness gives local compactness of the intersection. Choose regular left
Haar measures on both groups. The published
`Haar.compactOpenCoverUnimodularity` proves right invariance for these
measures from the derived compact open cover, including its closed subgroup
clause. Published `QuotientIntegration.compatibleMeasureExists` then gives
a genuine quotient measure. Its compatibility supplies regularity, hence
finiteness on compact subsets, right translation invariance, nonzero mass,
integrability of subgroup averages and the exact complex Weil formula.

All content is derived from the named published constructions and the
independently reviewed actual orbit kernel transport. No quotient measure,
right invariance, countability, total finite mass, scaling equation or
comparison is assumed. The existential measures are independent of any
coefficient representation. The later representation comparison and its
naturality remain separate obligations.
