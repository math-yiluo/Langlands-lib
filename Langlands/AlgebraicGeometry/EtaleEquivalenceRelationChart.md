# Étale chart relations

Author: Worker 706.

This internal construction restricts the published étale equivalence relation
`E` along a scheme morphism `f : V → E.U`. Its arrow scheme is
`(V ×_{E.U,t} E.R) ×_{s,E.U} V`. If `f` is étale, the induced endpoint
maps are étale and this is an étale equivalence relation on `V`.
The construction is derived from the Library axioms and fibre products. It is
the scheme-level chart operation used in the presentation route motivated by
Stacks Project Tag 07ST, registered as
`stacks-noetherian-approximation-2026-11-01`, and Tag 0BBN, registered as
`stacks-stratification-2026-11-02`. No quotient or approximation theorem is
assumed.

In namespace `EtaleEquivalenceRelation.Chart`, `arrows E f` is this double
fibre product, `t` and `s` are its endpoints in `V`, and `map` forgets the
chosen lifts to `V` and maps to `E.R`. The identities `map_t` and `map_s`
express compatibility with the original endpoints.

`lift` constructs a chart arrow from two morphisms to `V` and an original
arrow whose endpoints are their images under `f`. The equations `lift_t`,
`lift_s`, and `lift_map` recover those three inputs.
`hom_ext'` proves uniqueness from these three maps by the universal
properties of the two fibre products. `hom_ext` needs only the endpoints:
the original relation is a monomorphism in its absolute square, so the
original arrow is then unique as well.

`isPullback_pair` identifies the induced relation map into `V × V` with the
base change of the original relation map into `E.U × E.U` along `f × f`.
The proof constructs its universal lift explicitly. Thus
`isClosedImmersion_pair` preserves closedness of the relation.
`isAffine_arrows` proves that the arrow scheme is affine if `E.U`, `E.R`,
and `V` are affine. `etale_t` and `etale_s` prove étaleness of the two
endpoints when `f` is étale, by base change and composition.

`EtaleEquivalenceRelation.chart E f` packages this relation for an étale
`f`. Its monomorphism follows from `Chart.hom_ext`. Reflexivity, symmetry,
and transitivity are obtained by lifting the original unit, inverse, and
composition constructed in `EtaleEquivalenceRelationGeometry`. All
constructions preserve the arbitrary scheme universe `u`.
