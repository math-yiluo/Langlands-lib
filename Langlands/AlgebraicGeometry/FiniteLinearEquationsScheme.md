# Scheme representation of finite homogeneous linear equations

Let `R` be any commutative ring and let `a : Fin m → Fin n → R` be a
finite matrix. `equationsScheme a` is the actual spectrum of
`CoordinateRing a`, with its map to `Spec R` induced by the coefficient
algebra map. Its structure map is affine because its source and target
are affine. It is locally of finite presentation because the coordinate
algebra is finitely presented. Zero rows and zero variables are allowed;
there are no noetherian, field, or flatness hypotheses.

For every actual scheme `T` over `Spec R`, `sectionScalars T` composes the
inverse global-sections isomorphism of `Spec R` with the pullback along
`T.hom`. `sectionsAlgebra T` supplies precisely this algebra structure on
`Γ(T.left, ⊤)`. It is an explicit definition, used as a local instance in
this file. `pullSections q` is the scalar-compatible map on global
sections induced by any scheme morphism over the coefficient spectrum.
Its scalar compatibility follows from the commuting triangle in the
slice.

`schemeAlgebraPointsEquiv` identifies actual scheme morphisms over the
base with algebra maps from the coordinate ring into these global
sections. The forward map pulls back functions from the spectrum; the
inverse passes through the canonical morphism from `T.left` to the
spectrum of its global sections. Naturality of `ΓSpecIso` proves the
commuting triangle and both inverse identities. This uses the
Gamma-Spec adjunction for every scheme `T`, including nonaffine tests.

Composing this equivalence with the quotient algebra's `pointsEquiv`
gives `schemePointsEquiv`. Its coordinate formula is the image of the
corresponding quotient variable under the actual map on global
sections. `schemePointToAlgebra_comp` and
`schemePointsEquiv_naturality` prove compatibility with every restriction
in the scheme slice.

`solutionsPresheaf a` assigns to each such test the explicit
`ULift.{u + 1}` of its vectors of global sections satisfying all row
equations; the coefficient of each row is pulled back by that test's
structure morphism. Its maps pull back each coordinate using
`pullSections`. The functor laws follow from the functoriality of global
sections. `solutionsPresheafIso` packages the point equivalences as a
natural isomorphism from the lifted Yoneda functor of the actual equation
scheme. Its component coordinate formula records the same actual
pullback of each quotient variable, with the value lift intact. Thus the
representation is on the entire slice over `Spec R`.

The original source is the final paragraph of Stacks Project Lemma
99.3.8, Section 99.3 (Tag 08JS), retained in registered source
`stacks-hom-functor-08js-2026-11-02`, folder SHA-256
`2d60cda5ae13d9daa5c318ca4cd199e47a3a00b39f5062492b2207f7b56432c4`.
There the finite-matrix solution functor on all schemes is represented by
this quotient spectrum. The present unit is a derived expansion of that
step using Mathlib's Gamma-Spec adjunction, the coordinate-algebra unit,
and the affine and finite-presentation criteria for spectrum maps. The
retained full section and its two typo-only comments were read; no project
errata entry was found.

This unit represents finite linear solutions. The geometric construction
of a finite linear model for actual coherent-family Hom, including
perfect approximation and descent over arbitrary bases, remains an
additional obligation in the proper-Hom proof.
