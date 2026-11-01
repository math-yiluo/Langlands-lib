# The presheaf of compatible two-axis-rigidified line-bundle classes

Let `S : Scheme.{u}` and `A : AbelianScheme S`. This module constructs
the presheaf on `Over S` whose value at `T` is the set of isomorphism
classes of actual line bundles with compatible trivializations along
both unit axes of the actual self-product of `(baseChange T.hom).obj A`.
The construction has no additional coherence premise.

## The actual family

In namespace `TwoAxisFamily`, `abelian A T` abbreviates exactly
`(AbelianScheme.baseChange T.hom).obj A`. Write `B_T` for this object.
Its actual underlying scheme is the chosen pullback `A ×_S T`, with
structure morphism `B_T.X.hom : B_T.X.left → T.left`.

For every `h : T → U` in `Over S`, `carrierMap A h` is the map
`B_T.X.left → B_U.X.left` obtained from the chosen pullback's universal
property, with projections

```text
carrierMap A h ≫ pullback.fst A.X.hom U.hom =
  pullback.fst A.X.hom T.hom

carrierMap A h ≫ B_U.X.hom = B_T.X.hom ≫ h.left.
```

`carrierMap_id` and `carrierMap_comp` prove identity and composition by
comparing these two projections; `carrier` packages the resulting
covariant functor to schemes. `unit_fst` specializes the published
`GroupScheme.identitySection_baseChange_fst` theorem to the actual
base-changed abelian scheme. With `unitSection_comp`, it proves
`unit_naturality`, again by comparison of projections:

```text
unitSection B_T ≫ carrierMap A h = h.left ≫ unitSection B_U.
```

`productMap A h` is the corresponding map from the actual self-product
`(mumfordProduct B_T).left = B_T ×_T B_T` to
`(mumfordProduct B_U).left = B_U ×_U B_U`. Its first and second
projections are respectively the first and second source projections
followed by `carrierMap A h`. The structure-map identity above verifies
the equality needed for the pullback lift.

`productMap_id` and `productMap_comp` compare the product projections
and use the corresponding carrier identities; `product` packages this
covariant functor. `first_naturality` and `second_naturality` give

```text
mumfordSection B_T ≫ productMap A h =
  carrierMap A h ≫ mumfordSection B_U

twoAxisSecond B_T ≫ productMap A h =
  carrierMap A h ≫ twoAxisSecond B_U.
```

Both proofs compare product projections and use `unit_naturality`
for the projection containing the unit section. The axes are exactly
the parameter-first `(id,e)` axis and the `(e,id)` axis defined in the
paired `TwoAxisRigidification` module. No alternate model of the
self-product or theorem about iterated base-change identifications is
assumed.

## Categories, classes and the presheaf

In namespace `TwoAxisRigidifiedLineBundle`, `relative A T` is the category

```text
TwoAxisRigidifiedLineBundle
  (unitSection B_T) (unitSection B_T)
  (mumfordSection B_T) (twoAxisSecond B_T)
  (twoAxis_unit_comp B_T).
```

Thus a representative retains its actual locally free rank-one module
on `B_T ×_T B_T`, both chosen axis isomorphisms, and their compatibility.
Morphisms preserve both chosen trivializations.

`relativePullback A h` uses the canonical two-axis line-bundle pullback,
with four maps `productMap A h`, `carrierMap A h`, `carrierMap A h`,
and `h.left`. The preceding naturality lemmas supply every commuting
equation. `relativePullbackId` combines the proved carrier and product
identity equations with the unconditional line-bundle identity comparison.
`relativePullbackComp` combines the unconditional composition comparison
with the proved carrier and product composition equations. Consequently
these comparisons are isomorphisms in the categories retaining both
rigidifications.

`Classes A T` is
`Quotient (isIsomorphicSetoid (relative A T))`; it identifies two such
objects precisely when there is a compatible isomorphism between them.
It is not the quotient of ordinary line bundles with no chosen
rigidifications. `classesPullback A h` applies the actual functor
`relativePullback A h` on representatives. Its well-definedness follows
because a functor carries isomorphisms to isomorphisms.

Finally,
`classPresheaf A : (Over S)ᵒᵖ ⥤ Type (u + 1)` uses these classes and
pullbacks. Quotient induction reduces its identity and composition laws
to the component isomorphisms of `relativePullbackId` and
`relativePullbackComp`. No coherence proof is an argument to this
presheaf, and all its maps come from actual module-sheaf pullback.

## Provenance and limits

This is internal categorical infrastructure. The quotient construction
follows the published one-axis `RigidifiedClassPresheaf`. The compatible
pullback and unconditional comparisons come from
`TwoAxisRigidifiedLineBundle` and `RigidifiedPullbackProofs`; all family
map identities are proved here using scheme pullbacks and the published
base-change identity-section lemma. There is no new literature assertion.

The construction is uniform in `u`, every base scheme `S` and every Library
abelian scheme `A`; test-scheme maps are unrestricted. It asserts no
comparison with ordinary Picard classes or correspondence classes, fppf
sheaf property or sheafification, representability, gluing, extension
over valuation rings, or extraction of an actual total-space bundle
from a generic class.
