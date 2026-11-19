# Transfer of the proper-region bounds to the original compact picture

`standardLeviPacketChangeCompactLevel` specializes the transport of actual
orbit sections to the standard-Levi data. It views a section of level `H`
for `K` at level `H ⊓ L` for the other compact open Iwasawa factor `L`.

`standardLeviPacketProperRegionDerivativeEstimates_of_compactChange` proves
that the original packet satisfies the proper-region derivative estimates
whenever they are proved for the same data with compact picture `L`. It
compares the packet values by the positive compact probability ratio from
`RationalOrbitPacketCompactChange`, compares the two `rationalXi` functions
by `exists_rationalXi_le_mul`, and replaces the finite supremum of new
seminorms by a finite supremum of original ones using
`exists_orbitSectionLevelChangeCompact_finsetSup_bound`. The full matrix
height, proper-Levi regions and thresholds are the same. The Plancherel
weight, its continuation compact `Ks`, and the source-normalized measures
are shared by the two packets.

This derived transfer lets the proper-region proof of Waldspurger VI.3.1
use one compact subgroup with the required standard-Levi intersections.
The theorem takes the proper-region estimate at that subgroup as a premise.
