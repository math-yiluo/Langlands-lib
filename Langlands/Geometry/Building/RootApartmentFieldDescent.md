# Actual apartment descent by literal field restriction

For an arbitrary extension of fields in a common universe, this internal
construction starts with a smooth affine actual group, a monomorphic
split-torus inclusion with original opposite factor pairs, a homomorphism
from upstairs field units to additive real values, and a supplied upstairs
`KPApartmentData` compatible with that homomorphism. Its real values must be
nontrivial on the original field units. It constructs an actual downstairs
apartment and identifies its points affinely with those of the supplied
upstairs apartment. Its scalar compatibility is the literal restriction
along the original field-unit extension map.

`KPApartmentData.fieldRestrict` defines the carrier as the literal image of
the upstairs carrier under `RootFunctionFamily.fieldRestrict`. Full valuation
field descent proves all valuation laws for a base point, including V3
without an additional commutator premise. Split-torus compatibility descends
by actual character evaluation. Translation equivariance and surjectivity of
the actual real cocharacter base-change equivalence show that the carrier is
exactly one full downstairs translation orbit. Upstairs normalizer stability
and actual field-restriction equivariance prove downstairs normalizer
stability. Thus this is the existing `KPApartmentData` structure on original
objects, with all its fields supplied.

`fieldRestrictPoint` is the literal family restriction on each point.
Its real affine coordinate law uses the actual
`splitTranslationBaseChange` equivalence on reduced translation spaces.
The normalizer identity extends the original normalizer point by the actual
`normalizerPointsFieldExtend` homomorphism before applying the upstairs
action, then restricts to the unchanged original action.

The point map is surjective by its image-carrier definition. For injectivity,
two upstairs points differ by an actual translation. Pull that vector back
through real cocharacter base change. If their restricted families agree,
the downstairs valuation's translation stabilizer puts that vector in the
original root annihilator. Actual root-annihilator reflection puts its
extension in the upstairs annihilator, so the original upstairs points
agree. `fieldRestrictAffineEquiv` packages the resulting bijection as an
affine equivalence, whose linear part is the inverse of actual reduced
translation base change. No arbitrary coordinate identification is chosen.

`filtration_fieldRestrictPoint` states equality with the subgroup preimage
under actual `rationalExtend` for every original nonzero character and every
real bound. This follows directly from literal single-root filtration
reflection at that apartment point. The nonzero-character premise is
explicit; actual roots satisfy it. No root-system reduction or exclusion of
doubled roots occurs.

The provenance is full root-valuation field descent, actual character,
cocharacter, root-annihilator and normalizer base-change comparisons, and the
existing orbit apartment construction and translation-stabilizer theorem.
All are internal compositions; no new external assertion is introduced.
This unit retains the initial upstairs apartment and original opposite
factor pairs. It does not establish inhabitance of the upstairs data, a
building quotient comparison, affine-root or facet descent, the five
geometric axiom witnesses, or the supplied-model building comparison.
