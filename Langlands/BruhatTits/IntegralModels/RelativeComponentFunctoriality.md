# Functoriality and coefficient recovery of supplied neutral models

This internal result constructs maps between actual relative identity-component
models from maps between their supplied smooth full models. A compatible
isomorphism of full models recovers the neutral models, their inclusions, and
their exact integral-point images. Both constructions preserve the specified
identifications with the original generic group.

The base ring `R` is any commutative domain and `K` is its fraction field, both
in arbitrary universe `u`. There is no characteristic, valuation, local-ring,
or simply connectedness assumption. The input `RelativeComponentModelData`
contains smooth affine full and neutral integral models, a generic-identity
inclusion, and the all-test-scheme relative identity-component criterion.

`RelativeComponentFunctorialityStatement` has two clauses for every pair `D,E`
of such data with the same generic group `G`:

1. Every actual full-model homomorphism extending the identity of `G` has a
   unique compatible neutral-model homomorphism, and the inclusion square
   commutes.
2. Every compatible full-model isomorphism over the identity of `G` induces a
   compatible neutral-model isomorphism with commuting inclusion square and
   equality of the original neutral integral-point subgroups in `G(K)`.

`relativeComponentFunctoriality` proves this proposition. The module also
provides the coefficient-base-change constructions described below; those are
additional declarations rather than extra clauses of the proposition.

## Implemented proof

`neutral_geometricallyConnected` applies the published
`RelativeIdentityComponent.smoothExistence` to the full model. Uniqueness of
relative identity-component representatives transfers geometric connectedness
from that representative to the supplied neutral model using
`IsRelativeIdentityComponent.geometricallyConnected`.

`toNeutral` starts with a compatible map from any geometrically connected
integral model to the full model. The published
`RelativeIdentityComponent.factor` constructs its actual group-scheme
factorization through the supplied neutral inclusion. Its factorization
equality, after generic base change, and the inclusion's `generic_comm` prove
that this map retains the specified generic morphism. `ofFull` applies this
construction to the composite of the source neutral inclusion and the supplied
full-model map. `existsUnique_neutral` uses the published generic rigidity of
flat affine integral-model homomorphisms for uniqueness.

`neutralIso` restricts the forward and inverse full-model maps and applies
`IntegralModel.Iso.ofHoms`. Generic rigidity proves the resulting maps inverse.
`neutralIso_hom_comp` retains the inclusion square. The existing
`IntegralModel.Iso.integralPoints_eq` then yields the exact subgroup equality;
this is an equality of images of integral sections under the supplied generic
identifications.

## Coefficient base change

For a commutative domain `A` with fraction field `L`, the coefficient construction
assumes algebra structures and scalar towers giving the commuting square
`R -> A`, `K -> L`. All four rings lie in universe `u`.

`D.baseChange A L` uses the published `IntegralModel.baseChange` for both actual
models, their coefficient-square generic identifications, and the actual
pullback of the inclusion. Smoothness is preserved under base change. The
neutral model has geometrically connected fibres by the first argument, so its
pullback has connected fibres and
`IsRelativeIdentityComponent.baseChange` proves that it is the relative
identity component of the pulled-back full model.

`baseChangeNeutralIso` applies `neutralIso` to this pulled-back data. Thus a
supplied compatible isomorphism from `D.full.baseChange A L` to another full
model recovers `D.neutral.baseChange A L` as that model's supplied neutral
representative. `baseChangeNeutralIso_hom_comp` identifies the actual pulled-back
inclusion square, and `baseChange_neutral_integralPoints_eq` gives the exact
upstairs neutral integral-point equality.

## Provenance and scope

This is a deduction from the published Library interfaces in `RelativeComponent`,
`ConnectedFactorization`, `ModelMorphism`, `GenericRigidity`,
`SemilinearCoefficientDescent`, `SmoothIntersection`, and
`RelativeIdentityComponent.SmoothExistenceProof`. It supplies a connection needed
when using descended full models in building arguments. It assumes the actual
full models and any full-model recovery isomorphism; it constructs no parahoric
model, descent isomorphism, building fixer identification, or residue-parabolic
correspondence. In particular it does not prove the prescribed-point split-torus
statement. No descended-building statement is an input to these deductions.
