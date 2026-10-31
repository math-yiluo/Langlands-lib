# The Harris determinant condition on actual rational action classes

This module descends the constructed Harris rational Lie determinant predicate
to actual equivariant rational isomorphism classes over a fixed scheme mapping
to the constructed reflex field. It constructs the subtype of classes satisfying
that predicate and characterizes its equality and actual representatives.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines an isogeny as an invertible rational
homomorphism. Section III.1, printed pp.90–91 / PDF pp.98–99, uses actual
abelian schemes, actions in their rational endomorphism algebras and equivalence
by intertwining rational isogenies in its PEL moduli problem. The registered
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
section 5, printed pp.389–391 / PDF pp.17–19, constructs the Hodge/reflex
polynomial and requires equality with the polynomial on the actual relative
Lie algebra. It also uses equivalence through intertwining isogenies.
The registered source is `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

The present construction is derived infrastructure. It combines the actual
quotient in `RationalAlgebraActionClasses` with the all-chart isomorphism
invariance in `RationalLieDeterminantCondition`. It preserves that predicate:
every finite family in the constructed order, every finite local Lie chart,
and every smaller open must satisfy equality with the constructed reflex
polynomial through the actual structure morphism. It does not replace this
condition by the choice or existence of one chart.

This is the determinant restriction of the action-only quotient over a fixed
base. It is not identified with Harris–Taylor's full compatibility condition or
with either source's complete moduli functor. The action is not required to be
faithful, and relative dimension, polarization, involution compatibility,
monodromy-invariant level data, and their equivalence laws remain additional
obligations. No nonemptiness, smallness reduction, moduli representability,
scheme level, sheaf condition, or arbitrary-base-change stability is asserted.

## Well-definedness on actual classes

`harrisRationalLieDeterminantCondition_actionIso` applies the existing
isomorphism invariance theorem to the actual rational isomorphism underlying an
equivariant isomorphism. Its action equation is exactly the defining
intertwining equation of the actual action category. The supplied isomorphism
includes its actual rational inverse and both inverse identities.

`HarrisRationalLieDeterminantClassCondition` uses `Quotient.lift` into `Prop`.
Propositional extensionality applied to that invariance theorem proves the
required equality on related representatives. Consequently
`harrisRationalLieDeterminantClassCondition_classOf` is a definitional
equivalence with the original all-chart predicate on an actual representative.
The variant `..._iff_of_classOf_eq` gives this equivalence for every specified
representative of a class. The existential characterization `..._iff_exists`
uses the surjectivity of the actual quotient map, and its converse uses the
same representative equivalence. No choice of a preferred abelian scheme is
used to define the predicate.

## The restricted class type

`HarrisRationalLieDeterminantClass` is the subtype of actual rational action
classes satisfying the descended predicate.
`harrisRationalLieDeterminantClassOf` constructs an element from an actual
abelian scheme with action and a proof of its all-chart determinant condition.
Its underlying class is exactly the original action class.

The two `...ClassOf_eq_iff` lemmas say that equality is equivalent to an
actual equivariant rational isomorphism, or equivalently to an actual rational
isomorphism whose forward map intertwines every element of the algebra.
Subtype extensionality reduces both statements to the previously constructed
actual quotient relation. The inverse is part of the isomorphism; no arbitrary
integral homomorphism is declared invertible. The representative theorem
`...ClassOf_surjective` shows that every restricted class has an actual
representative satisfying the original condition, without proving that such
classes exist for any particular base.

Finally, `...ClassCondition_classOf_iff_integral` recovers the existing integral
condition when an actual integral order action is given and its image under
`endToEnd0` agrees elementwise with the rational action on the order. The
agreement is an explicit hypothesis, and the proof is the existing integral
specialization of the all-chart rational condition.

All arithmetic types, base schemes and the finite families and local charts in
the determinant predicate are universe zero; the resulting class type lies in
`Type 1`. The generic action-class presheaf can pull back unrestricted action
classes. Restricting its maps to this subtype requires a separate proof that
the actual Lie determinant condition is preserved by base change, including
the necessary naturality of the actual Lie comparison. This module does not
construct that restricted presheaf.
