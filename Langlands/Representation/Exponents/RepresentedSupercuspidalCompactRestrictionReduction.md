# Structural reduction for represented supercuspidal compact restriction

`RepresentedSupercuspidalCompactRestrictionReductionStatement` asserts that
the four universal propositions `ParabolicDynamicStatement`,
`StandardCocharacterStatement`, `RelativeRootSystemStatement`, and
`JointSpecialCompactBasisExistenceStatement` imply compact smooth-dual
coefficients after restriction to the actual subgroup
`Plancherel.rationalCommonNormKernel G`. The representation has vanishing
normalized Jacquet modules for every proper actual rational parabolic, with
a rational Levi and matching geometric unipotent radical. Its coefficients
are tested against every linear functional smooth for the restricted
representation. The field and representation carrier have independent
universes. Rational points use `RationalPointFamily.pointTopology`, with
local compactness and the nonarchimedean group structure quantified as in
the represented-group targets.

The theorem `representedSupercuspidalCompactRestrictionReduction` proves
this implication. Neither irreducibility, admissibility nor a central
character is required for this compactness conclusion. The four structural
premises remain explicit. This pair supplies a conditional input for the
admissible supercuspidal subquotient argument; it does not prove the
unconditional represented VI.3.6 realization statement.

The proof follows the structural assembly in
`SupercuspidalCoefficientCompactSupportReduction`, replacing its final
full-central-quotient coefficient-norm argument by the published norm-kernel
smooth-dual coefficient argument. First choose a maximal split torus and a
generic cocharacter using their published existence theorem. The relative
root premise supplies the root system for that torus. The joint geometric
premise supplies a special vertex, its compact subgroup, the represented
torus centralizer and character comparison, a Cartan comparison, and the
simultaneous standard basis, all for the same torus and cocharacter.
`rationalPositiveCartanCover` gives the corresponding finite positive
Cartan cover. The affine canonical point topology is Hausdorff, and the
standard unipotent subgroups are closed by the published local-field
closedness theorem.

`isCuspidal_of_all_represented_parabolics` converts the given all-parabolic
Jacquet vanishing to cuspidality for the actual standard point-subgroup
family, using the parabolic-dynamic and standard-cocharacter premises.
Finally `compactSmoothDualCoefficients_normKernel_of_jointDetection`
combines that cuspidality, the compact subgroup, basis, Cartan cover and
`rationalCartanJointDetection`. Its published smooth-dual comparison
handles all functionals smooth for the restricted norm-kernel action.
Thus the result has compact support on that subgroup itself.

This is derived internal assembly of published interfaces and proofs,
motivated by the compact-restriction step in Renard VI.2.1 and its use in
VI.3.6. It makes no additional claim from the original literature and
leaves the structural existence and unconditional realization proofs to
their respective owners.
