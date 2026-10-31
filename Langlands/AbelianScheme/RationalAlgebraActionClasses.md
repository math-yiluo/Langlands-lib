# Isomorphism classes of actual rational algebra actions

This module forms the quotient of actual abelian schemes with rational algebra
action by actual equivariant rational isomorphisms. Actual geometric pullback
induces a presheaf on schemes, and restriction supplies a presheaf on schemes
over any fixed base. This isolates the action part of a later PEL moduli problem.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91 / PDF pp.98–99, uses equivalence classes of
abelian schemes with rational algebra action, polarization and adelic level
data. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Printed p.18 / PDF p.26 defines an isogeny as an invertible actual rational
homomorphism. The quotient here retains that convention through the actual
rational category, while imposing only the intertwining of the algebra action.

This is derived infrastructure. It uses Mathlib's `isIsomorphicSetoid` and
`Quotient.map`, and the actual action category and pullback comparisons of
`RationalAlgebraAction`. It does not supply a different generic quotient
construction or assume a moduli scheme. The algebra is any unital rational
algebra; its action need not be faithful. Polarizations, relative dimension,
Hodge or determinant conditions, adelic levels, smallness, and representability
are additional obligations. In particular this presheaf is not identified with
the complete Harris–Taylor functor, which the source formulates first for
pointed connected locally noetherian schemes and then for general locally
noetherian schemes.

## The quotient relation

`IsoClass S D` is exactly
`Quotient (isIsomorphicSetoid (RationalAlgebraAction S D))`.
`classOf` sends an actual object to its quotient class, and
`classOf_surjective` proves that every class has such a representative.
`classOf_eq_iff` identifies equality with the existence of an isomorphism in
that actual category.

`classOf_eq_iff_rationalIso` expresses the same relation without the category
wrapper. It requires an actual isomorphism of rationalized abelian schemes
whose forward map satisfies

```text
i_X(d) ≫ e.hom = e.hom ≫ i_Y(d)    for every d : D.
```

The isomorphism includes its actual inverse and both inverse identities.
The forward direction forgets an equivariant isomorphism and uses its
intertwining equation; the reverse direction uses `isoMk`, which derives
equivariance of the inverse from the forward equation. The relation does not
assert invertibility of arbitrary integral homomorphisms.

## Actual pullback and the presheaf laws

`pullbackClass b` applies the actual action-category pullback to a
representative. Mapping actual equivariant isomorphisms proves this is
well defined. `pullbackClass_classOf` identifies it on every representative.
The identity and composition laws follow by quotient induction: the actual
`pullbackIdIso` and `pullbackCompIso` identify the representatives in question.
Thus the two laws are strict equalities of classes, without requiring a
triangle or pentagon identity for a bundled category-valued pseudofunctor.

`isoClassPresheaf D` bundles these operations as a functor from
`Schemeᵒᵖ` to types. Its object and map formulas expose the original actual
quotient and pullback, with the contravariant order of base morphisms. Bases
lie in one universe `u`, the algebra in an independent universe `v`, and the
quotient types lie in `Type (max (u + 1) v)`. No smallness reduction of these
quotient types is asserted.

`isoClassOverPresheaf E D` restricts along the forgetful functor from schemes
over `E`. Its formulas retain the actual underlying base scheme and actual
underlying morphism. `isoClassOverPresheafBaseIso a` is the identity
comparison obtained when the fixed base is changed by `a : E' ⟶ E`;
composition with `a` leaves these underlying schemes and morphisms unchanged.
Forgetting the fixed-base structure is the only operation in that comparison.
This construction makes no sheaf, descent, or representability claim.
