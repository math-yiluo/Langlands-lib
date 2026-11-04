# Analytic data for the rational compact comparison

This internal unit derives the analytic inputs of
`RationalGeometricCompactComparison` from the original closedness,
nonarchimedean local compactness and unipotent compact-limit hypotheses.
It preserves the literal restricted projection kernel and nested stabilizer
intersection. Its final comparison is unnormalized and retains the actual
compact Haar character.

The ambient field and group scheme are arbitrary, with the same point topology
as the supplied topological instances. The construction does not require a
characteristic-zero or split-group hypothesis. The representation carrier
universe is independent of the field universe.

The measure construction and final equivalence assume that the ambient
point group is Hausdorff, locally compact and nonarchimedean, with closed
target radical and both original parabolics. These are retained structural
hypotheses; the unit does not prove them for every point topology.

Local compactness of the restricted kernel is transported through
`geometricCompactKernelEquiv` from the closed original radical. The nested
intersection is closed by continuous pullback of the original closed orbit
stabilizer, and hence is locally compact. Subgroups inherit the
nonarchimedean structure. The published `compactOpenSubgroupBasis` therefore
gives the exact kernel basis required by the integral comparison.

The compact-limit premise is used on the original radical. The published
`CorrectedFiltration.exists_compactOpen_mem_of_isLimitOfCompactSubgroups`
places each radical element in a compact open subgroup. Pullback along the
original-point kernel equivalence gives such a subgroup for every kernel
element. `Haar.compactOpenCoverUnimodularity` then proves right invariance
for each regular left Haar measure on the kernel and its closed nested
intersection.

All three measurable structures are the Borel structures of the original
kernel, intersection and left coset space. The two Haar measures use Mathlib's
regular Haar construction. The quotient measure is selected from the proved
`QuotientIntegration.compatibleMeasureExists` applied to these actual measures
and the actual closed intersection. Its compatibility theorem retains
nonzero mass, regularity, right invariance, averaging integrability and the
complex Weil integral formula. In particular it is finite on compact sets.
The measure choices depend on the subgroups and structural hypotheses, and
not on the input representation.

`geometricCompactEquivOfCompactLimit` applies the published
`geometricCompactEquiv` to these choices. The original ambient parabolic's
compact open basis follows directly from its closedness. The remaining
arguments are exactly the existing structural normalizer comparison,
semidirect decompositions, actual source and target intersection
decompositions, closed target Levi, continuous projections and smooth
inducing representation. No orbit comparison, geometric expansion or
class equation is assumed.

In the final declaration's type, a local instance fixes the kernel's
derived local compactness proof, while the kernel and intersection use
their Borel structures. The compatibility theorem similarly fixes the
proved right invariance of the selected intersection measure before
forming `IsCompatible`. These local instances add no premises.

The proof bodies use subgroup topology, the compact-open cover argument,
Haar and quotient measure existence, and the already constructed actual
compact comparison. The imported closure includes the original coefficient
and split-stage constructions through `RationalGeometricCompactHaar`.
This unit adds no use of adjointness, cuspidal support, character independence
or Langlands classification. The normalization balance between the two
radicals, smooth-category naturality, compact/full induction, actual
filtration and final normalized K0 expansion remain separate obligations.
