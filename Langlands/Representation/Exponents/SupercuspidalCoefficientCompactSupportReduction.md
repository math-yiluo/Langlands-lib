# The structural inputs for represented-parabolic coefficient compactness

Authors: Worker 1742 and Worker 1276. Worker 1270 supplied the dynamic-parabolic
recognition theorem used by the stronger represented-standard adapter.

`SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement`
is the implication from the three explicit universal propositions
`StandardCocharacterStatement`, `RelativeRootSystemStatement`, and
`JointSpecialCompactBasisExistenceStatement` to the published, unchanged
`SupercuspidalUnitaryCoefficientCompactSupportStatement`.
The theorem `supercuspidalUnitaryCoefficientCompactSupportStructuralReduction`
proves this implication. The three structural premises remain inputs to the
reduction.

The conclusion preserves the original telescope: an arbitrary nonarchimedean
local field with Hausdorff topology, a connected reductive group scheme,
its rational points with their canonical topology and the assumed local
compactness and nonarchimedean group structure, an irreducible smooth complex
representation with vanishing normalized Jacquet modules for every proper
actual represented rational parabolic, and a prescribed unitary central
character. The field and representation carrier have independent universes.
The support is on the quotient by the full abstract center. Irreducibility
is retained in the conclusion but is not used by this proof.

The proof first uses the published existence of a maximal split torus with
a generic cocharacter. The relative-root-system premise gives a realization
for that torus. The joint geometric premise provides a single special vertex,
its compact subgroup, the represented torus centralizer, its character
comparison, the Cartan comparison, and the simultaneous standard basis, all
with the same torus and cocharacter. Compactness is extracted from the special
compact properties. `rationalPositiveCartanCover` converts that witness's
Cartan comparison into a finite positive Cartan cover for the same subgroup.
Hausdorffness of the rational-point group follows from the canonical affine
point topology, and the standard unipotent subgroups are closed by the
published local-field closedness theorem. The relative-root realization
also supplies the finite enumeration of actual simple roots.

`isCuspidal_of_all_represented_parabolics_of_standardCocharacter` uses the
standard-cocharacter premise to identify the actual standard subgroup
functors with dynamic parabolics, centralizers and unipotent subgroups on
every test scheme. The proved
`isParabolicSubgroup_of_range_eq_dynamicParabolic` recognizes the closed
standard parabolic representative from its dynamic range equality. The
adapter's other proved geometric comparisons identify its rational Levi,
geometric unipotent radical and multiplication isomorphism; its
relative-root argument proves properness for every proper standard face.
The original represented-parabolic vanishing hypothesis therefore applies.
The adapter's canonical linear equivalence preserves the class of each
original vector in the unipotent coinvariants, so the representation is
cuspidal for the actual standard point-subgroup family.

Finally, `compactUnitaryCoefficients_centerQuotient_of_isCuspidal` combines
this cuspidality with the chosen simultaneous basis and finite Cartan cover
to give the compactly supported descended coefficient norm for each smooth
dual functional and vector.

The earlier
`SupercuspidalUnitaryCoefficientCompactSupportReductionStatement` retains
its original four-premise definition, with `ParabolicDynamicStatement`
preceding the three premises above. Its theorem
`supercuspidalUnitaryCoefficientCompactSupportReduction` is a compatibility
wrapper: it discards the parabolic-dynamic argument and applies the stronger
reduction. The stronger proof needs the proved dynamic-to-geometric
direction, so it assumes no forward classification of arbitrary geometric
parabolics.

This is derived internal assembly of the imported interfaces and proofs.
It introduces no new claim from the literature. Proving the three retained
structural premises remains necessary to obtain an unconditional theorem by
this route. The module records reductions for the Renard VI.2.1 task; it
does not prove the unconditional coefficient-compactness statement.
