# Norm-defined depth-zero groups and canonical zero point fixers

This internal comparison uses the actual `moyPrasad` group from
`KPLocalMoyPrasadGroups` at depth zero, at arbitrary universe `u` and for every
supplied building datum `B` and zero datum `E`. Its torus term is the existing
norm-Iwahori term `centralizerTorusImage hZ 0`.

The definition `moyPrasadZeroToZeroPointFixer` is the canonical subgroup
inclusion from that depth-zero group into the canonical zero point fixer. It
preserves each underlying ambient rational point and needs no sharp-comparison
premise.

The theorem `moyPrasad_zero_le_zeroPoints_inf_fixer` proves unconditional
containment in the canonical zero subgroup intersected with the fixer of the
specified apartment point. It applies
`wholeApartmentZeroFixer_sup_sharpFixer_le` to the singleton and rewrites the
whole-apartment term with
`wholeApartmentZeroFixer_eq_centralizerTorusImage`. The definitions of
`moyPrasad`, `pointwiseFixer_singleton` and `sharpFiltration_zero` then identify
the two sides.

The theorem `zeroPoints_inf_fixer_eq_moyPrasad_of_sharpComparison` proves equality
conditional on the existing
`UnramifiedZeroFixerSharpComparisonStatement`. A singleton is nonempty and the
image of a singleton under every real affine functional is bounded above, so
the supplied assertion applies. The same three rewrites give the claimed
equality.

This module is a derived comparison among Library constructions. It does not
prove the sharp-comparison premise or the exact unconditional
`UnramifiedComparisonZeroFieldStatement`. Those obligations remain separate.
