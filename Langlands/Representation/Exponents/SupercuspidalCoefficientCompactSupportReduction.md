# The structural inputs for represented-parabolic coefficient compactness

`SupercuspidalUnitaryCoefficientCompactSupportReductionStatement` is the
implication from the four explicit universal propositions
`ParabolicDynamicStatement`, `StandardCocharacterStatement`,
`RelativeRootSystemStatement`, and
`JointSpecialCompactBasisExistenceStatement` to the published, unchanged
`SupercuspidalUnitaryCoefficientCompactSupportStatement`.
The theorem `supercuspidalUnitaryCoefficientCompactSupportReduction` proves
this implication. It does not prove its four premises or the unconditional
coefficient compactness statement.

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
published local-field closedness theorem.

`isCuspidal_of_all_represented_parabolics` uses the explicit parabolic-dynamic
and standard-cocharacter premises to apply the original represented-parabolic
vanishing hypothesis to every proper standard face. Its canonical linear
equivalence preserves the class of each original vector in the unipotent
coinvariants. Thus the representation is cuspidal for the actual standard
point-subgroup family. Finally,
`compactUnitaryCoefficients_centerQuotient_of_isCuspidal` combines this
cuspidality with the chosen simultaneous basis and Cartan cover to give the
compactly supported descended coefficient norm for each smooth dual
functional and vector.

This is derived internal assembly of the imported interfaces and proofs.
It introduces no new claim from the literature and leaves every structural
existence premise visible. The module records a proved reduction for the
Renard VI.2.1 task, not completion of that task.
