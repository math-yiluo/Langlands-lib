# Section determinants of rational actions on actual relative Lie modules

This internal construction applies [LieRational](LieRational.md) and
[LocalSectionIso](../AlgebraicGeometry/LocalSectionIso.md) to the published
section determinant construction. It introduces no additional existence
theorem. Worker 57 authored this file.

Let `S` be an actual scheme, `R` a commutative rational algebra, and
`p : S ⟶ Spec R` an actual base morphism. An actual abelian scheme `A` carries
a unital ring action `α : O →+* End0 A`; this action need not be injective.
`lieRationalLocalOrderAction` restricts its constructed relative Lie action
to an open `U`. `lieRationalSectionOrderAction` evaluates that action on the
actual sections over every object `V` of `Over U`. Naturality of the actual
module-sheaf morphisms proves compatibility with restriction of sections.

`lieRationalSectionDeterminant` uses a genuine finite free-sheaf chart on
`U` and its constructed finite section basis on `V.left`. It is the
multivariate determinant polynomial of a finite family in `O`, with
coefficients in `Γ(S,V.left)`. Any finite basis of the same section module
computes the same polynomial. The polynomial restricts along the actual
structure-sheaf maps, and its evaluation is the intrinsic determinant of
the corresponding scalar linear combination of section endomorphisms.
These properties specialize the published local section determinant
lemmas. They apply to section rings with nilpotents, including the zero ring.

If an integral action is followed by the actual map `endToEnd0 A`, the
constructed local action and determinant equal `lieLocalOrderAction` and
`lieSectionDeterminant`. The proof restricts the integral specialization
of the rational Lie action and substitutes it into the polynomial.

An actual isomorphism `e` in the rational category produces the actual
sheaf isomorphism `lieIso0 p e`. Its restriction is `lieLocalIso0 p e U`.
An intertwining equation for `e.hom` and the actual rational order actions
passes through the rational Lie functor and then through restriction.
Consequently `lieRationalSectionDeterminant_iso` compares arbitrary finite
charts of the two Lie sheaves on `U`, on every smaller open `V.left`. It
uses the published determinant transport through an actual local sheaf
isomorphism, including independence of the target chart.

The rational isomorphism includes an actual rational inverse. This unit
does not assert that every isogeny over an arbitrary base is rationally
invertible. It does not supply a Lie base-change naturality theorem.
Schemes and finite chart indices have universe `u`; the acting ring and
the finite polynomial family have independent universes `v` and `w`.
