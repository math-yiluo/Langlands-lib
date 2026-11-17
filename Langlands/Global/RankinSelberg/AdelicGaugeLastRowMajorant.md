# Compact last-row bounds in the simple-root gauge coordinates

This derived internal module specializes the compact-row majorant to the
published `gaugeDiagonalPoint` and `gaugeStandardCompact` on the actual
adelic general linear group-scheme points.

`isCompact_gaugeStandardCompact` transports compactness of the standard
adelic matrix subgroup through `GeneralLinearGroupPoints.adelicHomeomorph`.
`lastRow_gaugeDiagonalPoint` identifies the last row with the coordinate
row supported in the last position. The previously proved compact
diagonal-row estimate therefore gives one Schwartz–Bruhat function on a
one-dimensional row that bounds the last-row Schwartz factor for every
diagonal idele tuple and every point in a fixed compact family.

For the standard compact, `exists_standardCompact_lastRow_majorant` also
allows an arbitrary left adelic upper-unipotent factor. The published
`EqualUnfolding.lastRow_unipotent_mul` removes that factor before applying
the compact bound. Thus the resulting test function depends on the
original test function and compact subgroup, while its argument uses
only the last diagonal idele. No Iwasawa integration formula or global
convergence conclusion is asserted here.
