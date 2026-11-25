# Strict uniformizer images of actual standard Levi split components

`Langlands.GroupScheme.CocharacterUniformizer.standardLeviStrictImage` proves
the published
`Langlands.GroupScheme.CocharacterUniformizer.StandardLeviStrictImageStatement`
with all its parameters and hypotheses unchanged.

The helper `map_latticeSection` proves that evaluation of a cocharacter at
the common field uniformizer commutes with an actual commutative group scheme
morphism by associativity of composition. The helper
`characterNorm_latticeSection_lt_one_iff` uses the published norm formula
`characterNorm_latticeSection` and residue cardinality greater than one to
identify strict character norm inequalities with positive integral pairings.

The proof first constructs `t = standardLeviTorusFactor i ν J hj`, the actual
lift of the ambient maximal split torus through the supplied Levi
representative. Its composite with `j` is `i`, and it is maximal split in that
representative. Cancelling the monomorphism `j` in the supplied compatibility
square gives `groupHom f ≫ t = a`. Closedness of `j` supplies the affine and
finite-type instances needed for the published structural lemmas.

For the forward inclusion, a point of the strict section has a cocharacter
representative in the supplied split component. Its image has zero pairings on
the selected roots by
`latticePairing_cocharacterMapInt_standardLevi_eq_zero`, using `dynamicLie`.
Outside that index, `RelativeRoot.latticePairing_restrict_cocharacterMapInt`
identifies the restricted pairing with pairing against the image cocharacter,
so the strict inequalities give positive pairings.

For the reverse inclusion, the published standard-cocharacter centrality
theorem `IsStandardCocharacter.isCentral_standardLeviTorusFactor` makes the
given integral cocharacter central in the actual standard Levi representative.
The theorem `IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters`
then supplies an integral preimage under the compatible map. Its restricted
pairings are positive; `characterNorm_latticeSection_lt_one` therefore places
its uniformizer value in the existing strict section. `map_latticeSection`
gives the required equality of actual rational points.

This route preserves every parameter of the target, including arbitrary field
characteristic, supplied actual representatives and split components, and empty
root systems. It makes no quotient, finite generation or freeness claim and
does not infer integral factorization from an equality of real vector spaces.
It is a derived
comparison of the existing Library constructions, using the published structural
theorems named above. The source motivation is Renard, French edition dated
9 July 2026, V.2.5,
printed p.107 / PDF p.113, V.3.21, printed p.116 / PDF p.122, and V.3.23–V.3.24,
printed p.117 / PDF p.123. The target Markdown records the derived formulation
using actual group schemes and supplied compatible maps.
