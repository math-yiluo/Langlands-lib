# Descent of canonical zero point fixers along apartment lifts

This is derived internal infrastructure for Task 6666. It does not identify the
norm-Iwahori Moy–Prasad group with a canonical zero point fixer.

The module imports the unchanged published concrete-lift interface. Its theorem
`ApartmentLift.e_injective` follows directly from `L.restrict`: two lift points
that agree have equal restricted root-function families, hence equal downstairs
apartment points. The definition `ApartmentLift.eEmbedding` packages the actual
map `L.e` as an embedding `P.Apartment ↪ L.apartment.Apartment`, using this proved
injectivity; its underlying function is definitionally `L.e`. The theorem
`normalizer_smul_eq_iff` combines the embedding's injectivity with `maximalUnramifiedApartmentInjective` and `L.normalizer` to reflect fixation
by every downstairs normalizer point.

For every supplied unramified zero datum `E` of the upstairs group, the theorem
`comap_zeroPoints_inf_fixer` identifies the restriction of `E.zeroPoints` intersected
with the fixer of the actual point `L.e y` to `P.centralizerZero`. For the forward
inclusion, `E.zeroPoints_le_characterValuationKernel` and
`characterValuationKernelDescent_proof` put the ambient downstairs point in its
character norm kernel. Fixation reflects to the downstairs apartment, so
`ValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq` puts the
centralizer point in its own norm kernel.
`ZeroSubgroupDatum.comap_unramifiedZeroPoints_inf_centralizerNormKernel` then
gives membership in the centralizer-zero subgroup.

For the reverse inclusion, the published
`ZeroSubgroupDatum.zeroSubgroup_le_comap_unramifiedZeroPoints` gives upstairs
canonical zero membership, and
`ZeroSubgroupDatum.centralizerZero_le_rationalCommonNormKernel` together with
`P.isOmegaCompatible.smul_eq_self` gives downstairs fixation. The lift's normalizer
identity transfers that fixation upstairs.

The mathematical provenance is KP Definition 2.6.23(2), Corollary 9.7.3 and the
first paragraph of the proof of Lemma 9.8.1, through the named published Library
results. No apartment axiom hypothesis or existence of lifts is needed for these
auxiliary descent lemmas.
