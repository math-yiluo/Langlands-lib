# Actual split parabolic charts with unscaled face heights

This derived unit constructs actual split root charts whose auxiliary natural
weights are the unscaled integral face heights for the originally supplied
coordinate cocharacter. Zero weights are allowed. The base ring is arbitrary;
the ambient group is reductive, with a supplied fibrewise maximal coordinate
split torus, finite fibrewise root datum and actual root parametrizations.

`RootWeightData.isRepresentedBy_zeroInclusion_of_sameZero` transfers the
all-test ambient positive-term representation between two weight data on the
same regular chart when their zero roots agree. It constructs the comparison
isomorphism between the represented subgroups and uses its exact inclusion
equation to preserve their ambient ranges.

`SplitParabolicFaceChart` records the actual regular chart, its ambient root
labels and inclusion equations, a compatible positive base, the root-datum
coweight realizing the original coordinate pairing, dominance, unscaled face
weights and the all-test representation of the original contracting subgroup.
`nonempty_splitParabolicFaceChart` constructs every part of these data from
the reductive root-parametrization inputs; the representation is a proved
conclusion of this construction.

The proof chooses a base on which the original coordinate cocharacter has
nonnegative root pairings, then a regular cocharacter defining that positive
system. The actual open split big cell supplies its ordered regular chart.
The perfect root-datum pairing transports the original coordinate functional
to a root-datum coweight. On the chosen positive roots, the existing dominant
face-height vanishing and positivity results say that face weights and original
cocharacter weights have the same zero roots. The exact supported-coordinate
criterion therefore identifies their positive terms. The already proved
all-test dynamic representation for the original weights transfers to the
unscaled face-weight term.

`SplitParabolicFaceChart.dynamicIso` identifies this actual positive term with
the originally supplied contracting group. Its ambient equation is exact.
`hasFiniteVectorBundleSeries` applies the existing represented root-weight
series and isomorphism transport, so its series uses the unscaled based-face
weights, independently of denominator choices in the commutator proof.

Provenance is the existing actual split big cell, positive root chart,
independent-cocharacter dynamic comparison, integral face-height properties and
the unscaled root-span commutator construction. The chosen positive base,
regular cocharacter and root parametrizations need not be canonical. This unit
does not establish comparison under changing those choices or maximal tori,
nor global descent of the filtration.

The local affine-source instance has the explicit internal name
`splitParabolicFaceChart_affineSource`. This avoids an anonymous declaration-name
collision when this module is imported together with the global root parametrization
infrastructure. Its type, proof and local scope are unchanged.
