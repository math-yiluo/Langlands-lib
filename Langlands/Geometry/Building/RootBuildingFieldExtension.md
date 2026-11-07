# Actual scalar extension of the literal restricted building quotient

This internal construction takes fields `k → K` in an arbitrary common
universe, a smooth affine group over `k`, a monomorphic inclusion of an
original split torus, original opposite factor pairs, a real unit character
upstairs which is nonzero on some original field unit, and a supplied
upstairs `KPApartmentData` on the literal base changes. The source apartment
is precisely `KPApartmentData.fieldRestrict` of those data, with its exact
restricted scalar order and original normalizer action.

`fieldExtendPoint` is the inverse of the already proved actual affine
restriction equivalence. Its two inverse identities and injectivity follow
from that equivalence. `fieldExtendPoint_normalizer` proves its
equivariance for original normalizer points and their actual scalar
extensions: apply injective restriction and use the existing restriction
equivariance and the inverse identities.

`filtration_fieldExtendPoint` rewrites the existing exact filtration
preimage theorem by the inverse identity. Every nonzero original character
and every real bound are included, with the same bound upstairs.
`sharpFixer_le_fieldExtendSharpFixer` applies this comparison at depth zero
to each original relative root. Its actual pulled-back character is an
upstairs root by the existing root-support comparison. Each extended
generator therefore belongs to the corresponding upstairs root fixer and
hence its generated sharp fixer. The supremum over original roots proves
the subgroup inclusion. Composing with the already proved inclusion of an
upstairs sharp fixer into its reduced point fixer gives
`sharpFixer_le_fieldExtendFixer`. No reflection of generated sharp fixers is
asserted.

`fieldExtendBuilding` maps the existing source reduced quotient into the
existing upstairs reduced quotient. Its construction restricts the
upstairs group action along the actual rational-point extension homomorphism
locally. The apartment map sends a source point to the upstairs quotient
class of its extended apartment point. Its normalizer equivariance follows
from the proved point comparison and the existing upstairs apartment-map
equivariance. The proved sharp-fixer inclusion is the hypothesis of the
existing universal `ApartmentQuotient.lift`, which establishes
representative independence. Both required comparisons hold at every
source apartment point and are proved here, rather than supplied separately.

The representative and apartment formula theorems describe this exact
map, and `fieldExtendBuilding_smul` expresses equivariance with the
original upstairs action and actual scalar extension. No new global
restricted-action instance is exported. `fieldExtendBuilding_unique`
follows because every source quotient point is a group translate of an
apartment point, so equivariance and the apartment values determine it.

`fieldExtendBuilding_injective` retains common translated source
apartments and injectivity of the upstairs apartment map as explicit
geometric hypotheses. Under them, the existing universal-lift injectivity
theorem applies to the composite of the injective inverse affine
restriction and that apartment map. These geometric hypotheses are not
used to construct the quotient map.

The provenance is internal: actual apartment restriction, exact filtration
preimages, actual root-support base change, sharp fixers, and the existing
universal equivariant quotient lift. The unit does not construct initial
upstairs apartments or original opposite pairs. It concerns the literal
base change of one original split torus and makes no larger-torus
restriction assertion. It does not prove Galois fixed-locus surjectivity,
unconditional quotient injectivity, building axioms, a metric or continuity,
or the supplied-model point and fixer comparison required by
`BuildingComparisonStatement`.
