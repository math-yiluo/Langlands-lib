# A finite unipotent series from one-dimensional classification

This derived reduction assumes the existing propositions
`UnipotentClosedSubgroupStatement` and
`PerfectFieldOneDimensionalUnipotentStatement`. For a smooth connected affine
unipotent group scheme over an algebraically closed field in any universe
and characteristic, it constructs a finite series in the unchanged
`RelativeRoot.HasSplitSeries` sense. The two propositions are explicit
inputs; this module does not prove either of them.

`algebraicallyClosedSplit_of_oneDimensional` proves the existence of the
series. `algebraicallyClosedSplitSeries` chooses a length together with a
proof of the full represented-series predicate at that length, retaining
the same two inputs.

The proof uses the existing induction on proper smooth affine closed
subgroups. The inductive property asks for splitness under connectedness
and unipotence. If the identity homomorphism has bottom range, the series
has length zero; this is triviality on every relative scheme test.

Otherwise, the existing additive-character construction gives a nonzero
homomorphism to the standard one-dimensional vector group. Its actual
scheme kernel can be nonsmooth or disconnected. The proof instead uses
`KernelCoreQuotient.core`, the reduced identity component of that full
kernel, and the existing represented quotient by this specified core.
The core is smooth, connected, affine, closed and normal. Its inclusion
is proper because the homomorphism is nonzero. The closed-subgroup input
makes the core unipotent, and the induction hypothesis supplies its finite
series.

The published `affineGroupSchemeQuotient` proves affineness of the actual
quotient, using its flat, surjective, quasi-compact projection. The existing
kernel-core dimension theorem proves its smooth relative dimension is one.
Unipotence descends through this projection. Since an algebraically closed
field is perfect, the one-dimensional classification input supplies natural
one-dimensional vector coordinates on every test scheme. These coordinates,
the existing represented fppf kernel equality, and normality of the core
give one successor step of the required series.

This is an internal assembly of the cited Library constructions. No
classification of finite covers of the additive group is inferred from the
existence of such a cover. The result concerns algebraically closed fields;
it does not prove the stronger perfect-field splitness statement or the
host solvable-group statement.
