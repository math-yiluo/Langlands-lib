# The norm Iwahori as the whole-apartment zero fixer

This internal comparison is derived from published Library results. It adds no
building-existence hypothesis and uses every supplied unramified building datum
and every supplied zero datum at arbitrary universe `u`.

The definition `wholeApartmentZeroFixerEquiv` is the canonical multiplicative
equivalence from the whole-apartment zero fixer to the actual norm-Iwahori
image. It is induced by the subgroup equality proved below and preserves the
underlying ambient rational point.

`centralizerTorusImage_zero_eq_torusIwahoriImage` compares the actual zero term
of `KPLocalMoyPrasadGroups` with a zero datum whose maximal torus represents the
apartment centralizer. The unique isomorphism between centralizer
representatives, `centralizerTorusImage_eq_map_iso`, and
`localTorusFiltration_zero` identify the two norm images.

`wholeApartmentZeroFixer_eq_centralizerTorusImage` proves that the intersection
of the canonical zero subgroup with the pointwise fixer of the whole apartment
is that same actual norm-Iwahori image. It first replaces the torus in the zero
datum using `withApartmentTorus`; `withApartmentTorus_zeroPoints` preserves the
ambient subgroup. The generic whole-apartment fixer theorem puts every fixer
in the actual centralizer. The generic apartment embedding and
`mem_characterValuationKernel_of_mem_oneStabilizer` then show that its
centralizer representative has unit character values. Valuation equivalence
converts between the integer and fixed-field conventions.
`zeroPoints_comap_inf_characterValuationKernel_eq_torusIwahori` identifies this
intersection with the norm Iwahori. For the reverse inclusion, norm-Iwahori
points lie in zero points and have unit character values; the supplied V6
compatibility makes them fix the whole apartment.

The mathematical provenance is internal: the file composes the cited Library
comparisons for the norm-defined and canonical subgroups without asserting a
new independently sourced version of a KP statement.
