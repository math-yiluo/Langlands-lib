# Constructing the open relative identity subgroup

For an arbitrary scheme `S : Scheme.{u}` and actual group scheme
`G : GroupScheme S`, this module constructs a relative identity subgroup from
the following inputs:

- `hopen : IsOpen (underlyingSet G)`;
- smoothness of `G.X.hom`;
- geometric connectedness of the structure map of the open restriction
  `identityOver G hopen`.

The openness and geometric connectedness inputs remain explicit. The module
does not establish them for every smooth group scheme, so its final existence
theorem does not yet prove `SmoothExistenceStatement`.

## The open restriction

`identityOpen G hopen` is the open subset `underlyingSet G`, the union of the
identity connected components of the residue fibres.
`identityOver G hopen` is its actual open subscheme with structure map
`(identityOpen G hopen).ι ≫ G.X.hom`. The morphism
`inclusionOver G hopen` is the open immersion into `G.X` in `Over S`.
`range_inclusionOver` records its exact image.

The preliminary lemma
`inRelativeIdentityComponent_of_geometricallyConnected` applies to a
geometrically connected scheme `T` over `S`, an over-morphism `x : T ⟶ G.X`,
and a section `a` with `a ≫ x = η[G.X]`. Each residue fibre of `T` is
connected. Pulling back the section supplies a point mapping to the ambient
identity, so `IdentityComponent.range_subset_identitySet` puts the whole fibre
image in the identity connected component. This proves the published
`InRelativeIdentityComponent` criterion for `x`.

## Restricting the operations

`one_range_subset` applies this lemma to the unit section of `G`. The identity
map of `S` is geometrically connected: after pullback to a field its projection
is an isomorphism to that field's spectrum. The unit therefore lifts through
the open immersion, giving the actual map `openOne`.

Under the smoothness and geometric connectedness inputs, the open restriction
is smooth, hence universally open. Its fibre product with itself is
geometrically connected by base-change stability and
`GeometricallyConnected.comp`. The product of the two unit sections maps under
ambient multiplication to the ambient unit. The preliminary lemma thus proves
`mul_range_subset`, and lifting gives `openMul`. The same argument with the
restricted unit and the identity `one_inv` proves `inv_range_subset` and
constructs `openInv`. This inversion argument uses geometric connectedness and
does not require smoothness.

The equations `openOne_fac`, `openMul_fac`, and `openInv_fac` identify these
operations after inclusion into `G.X`.
`GroupObjectDescent.grpObjOfMono` transports the group laws along that
monomorphism, yielding `openGrpObj`. Its homomorphism lemma makes the inclusion
an actual group-scheme homomorphism.

## Representation and conditional existence

`groupOfIsOpen G hopen` is the resulting group scheme and
`inclusionOfIsOpen G hopen` its actual homomorphism to `G`. The source remains
smooth and geometrically connected over `S`, and the inclusion is an open
immersion.

`isRelativeIdentityComponent_inclusionOfIsOpen` applies
`IsRelativeIdentityComponent.of_range_eq_underlyingSet` to the exact image
equality. This gives the full representation predicate on every object of
`Over S`, including nonreduced and nonaffine test schemes.
`exists_of_isOpen` packages the constructed group, inclusion, representation,
smoothness and geometric connectedness into the existence conclusion for this
`G`. There are no restrictions on the base scheme or universe.

## Provenance and remaining obligations

This is internal derived content. The operation-restriction argument follows
the implemented construction in `Langlands.GroupScheme.IdentityComponent`,
with its field-specific connectedness arguments replaced by the explicit
relative hypotheses above. It uses the underlying-set criterion and image
constructor from `RelativeIdentityComponent.UnderlyingSet` and
`RelativeIdentityComponent.BaseChange`, the categorical group-law descent from
`Langlands.CategoryTheory.GroupObjectDescent`, and Mathlib's actual open
restrictions, pullbacks and geometric connectedness results. No new assertion
from external literature is assumed.

The unconditional openness and geometric connectedness results are still
needed for smooth existence. Once those inputs are proved for every smooth
`G`, the supplied existence conclusion and
`RelativeIdentityComponent.smoothStructure_of_existence` give the host task's
aggregate target. This module alone does not discharge that target.
