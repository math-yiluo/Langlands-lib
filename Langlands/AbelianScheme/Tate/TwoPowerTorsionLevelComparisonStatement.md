# Actual torsion levels in a closed abelian subscheme

`Langlands.AbelianScheme.Tate.TwoPowerTorsionLevelComparisonStatement.{u}`
asserts that an actual closed-immersion homomorphism `f : B ⟶ A` of abelian
schemes over a field induces a bijection on every existing actual torsion
level of order `2 ^ n`, provided its underlying image contains
`twoPowerTorsionLocus A`. The field and universe are arbitrary; algebraic
closedness and characteristic zero are not required.

The map in the conclusion is the existing `GroupScheme.Tate.levelMap`,
evaluated on the identity test scheme `Spec K`. Its source and target are
the existing additive groups of actual sections killed by `2 ^ n`. The
image hypothesis concerns the underlying scheme map `hom f` and the
existing section-defined point locus. It does not assume that this locus
is dense or that the closed immersion is surjective.

This is an internal geometric consequence of closed-immersion
factorization over a reduced field spectrum. Every ambient torsion section
has its unique underlying point in the image of `f`. Its whole range lies
there, so the section factors through `B`. Monomorphism cancellation and
compatibility with powers show that the lifted section is killed by the
same power of two. Cancellation also proves injectivity of the level map.

This file defines a proposition and requires a separate proof contribution.
The result can compare the actual levels of a torsion-closure realization
with those of its ambient abelian scheme. It supplies no such realization,
numerical torsion formula, equality of relative dimensions, or density
conclusion.
