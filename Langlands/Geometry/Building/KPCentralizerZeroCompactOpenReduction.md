# Compact openness of the actual centralizer-zero subgroup from openness

This internal derived unit reduces the exact target
`CentralizerZeroCompactOpenStatement` to openness of the actual supplied
centralizer-zero subgroup and three whole structural statements. It uses only
named Library interfaces and elementary topological-group facts. It does not
make an independent claim about any external source.

`CentralizerZeroCompactOpenReductionStatement` is stated for every
nonarchimedean local field `F` in arbitrary universe `u`, every group scheme
`G` over `Spec F` with affine structure morphism and every actual
`ParahoricBuildingData P` of `G`. It explicitly assumes the entire
`ActualCentralizerStructureStatement`, `CentralQuotientReductiveStatement` and
`AnisotropicCompactnessStatement` at the same universe `u`. It also assumes
that `P.centralizerZero` is open in exactly the canonical rational-point
topology `rationalPointTopology F P.centralizer.Z.X`, with the affine
structure derived from the supplied closed centralizer inclusion. Under these
inputs it concludes `P.CentralizerZeroCompactOpenStatement` itself, so the
topology and instances agree with those of the exact target.

`centralizerZeroCompactOpenReduction` proves this conditional proposition.

1. `actualCentralizerNormKernelCompactnessReduction` gives compactness of
   `rationalCommonNormKernel P.centralizer.Z` in the canonical topology.
2. The retained structure statement, applied to the actual data of `P`, makes
   `P.centralizer.Z` connected reductive, hence smooth. So
   `rationalPoint_isTopologicalGroup` makes its rational points a
   topological group.
3. In a topological group an open subgroup is closed. This is Mathlib's
   `Subgroup.isClosed_of_isOpen`, applied to the assumed openness of
   `P.centralizerZero`.
4. `ZeroSubgroupDatum.centralizerZero_le_rationalCommonNormKernel` places the
   actual centralizer-zero subgroup inside the norm kernel. A closed subset of
   a compact set is compact (`IsCompact.of_isClosed_subset`).

The openness half of the conclusion is the assumed openness.

The three whole-statement inputs and openness of `P.centralizerZero` remain
proof obligations. This unit proves none of them, so it does not prove
`CentralizerZeroCompactOpenStatement` unconditionally. Both local-field
characteristics and split rank zero are retained.
