# Actual torus restriction followed by field restriction

Work over an arbitrary extension `K/k` of fields in universe `u`, an actual
smooth affine group `G/k`, and a monomorphic split torus inclusion `i:S→G`.
Over `K` retain an actual split upper torus `T`, a monomorphic map `j:T→G_K`,
upper opposite factor pairs and a supplied root-datum valuation for `j`.
An actual torus morphism `f:S_K→T` satisfies `groupHom f ≫ j = i_K`.
Original opposite factor pairs for `i` are additionally required for V3.
No maximality of either torus or full lower-torus valuation over `K` is assumed.

`torusFieldRestrictedRootFunctionFamily` is the literal field restriction
of the previously constructed canonical torus-restricted scalar family.
`torusFieldRestrictedRootDepthSubgroup` is the exact preimage under actual
`rationalExtend` of the canonical subgroup at the pulled-back original
character and unchanged real depth. The finite-level theorem identifies each
original root filtration with this subgroup carrier.

`torusRestrictedRootDepthCollectionData_of_fieldFactorization` transports the
canonical torus collection data along the actual factorization equality.
`torusFieldRestrictedRootFunctionFamily_commutator` applies weak-data field V3
to those data. Its conclusion is exactly the original V3 inclusion, with the
closures of the original input filtrations and the closure of the union at
all actual mixed output roots and depths `p*r+q*s`. Both depths are arbitrary
reals; no full root-datum valuation on `S_K` is needed.

`torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible` derives
covariance from upper compatibility with a real additive unit character.
Canonical torus covariance gives the formula for `f≫j`; the factorization
equality identifies its map with `i_K`. Actual field restriction then gives
the formula for `i` and the restriction of exactly the same unit character
to the image of `k` units.

The provenance is internal composition of canonical torus collection data,
weak-data field commutator descent and actual torus/field covariance.
`SelectedRootDepthCollection` reuses the published stronger arbitrary-depth
lemma `IsRootDatumValuation.filtrationSubgroup_double_le` from
`PositiveDepthRayCompression`, specialized to doubled depth with `le_rfl`.
The integrated dependency also reuses the existing public pair-absorption
lemma. These consolidations preserve the reviewed statements and their
mathematical meaning. Prerequisite pairs retain their independent review
and publication obligations.
This unit does not establish initial/adapted existence, reflection V2,
opposite-root V5, the building geometry or the supplied-model comparison.
