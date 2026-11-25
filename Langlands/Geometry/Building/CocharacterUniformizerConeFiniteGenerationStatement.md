# Finite generation of the actual nonnegative uniformizer quotient

`Langlands.GroupScheme.CocharacterUniformizer.ConeQuotientFiniteGenerationStatement`
asserts finite generation of the existing actual quotient monoid
`CAplusQuotient F T (simpleRelativeRoots i ν) A f`.
The quantifiers and hypotheses are those of the published
`ConeQuotientComparisonStatement`: `F : Type u` is any nonarchimedean local
field, `G` is a connected reductive group scheme over `F`, `i : T → G` is
a maximal split torus, and `ν` is an actual generic cocharacter. The map
`a : A → G` is a split component, and `f : A → T` is any supplied
commutative-group-scheme morphism satisfying
`CommGroupScheme.groupHom f ≫ i = a`. The statement includes both field
characteristics, nonsplit reductive groups, nonreduced relative root systems
and rank zero. It does not require a coordinate presentation or a chosen
finite set of generators.

Put `R = simpleRelativeRoots i ν` and let `N` be the rational-point image of
`CA F A` under `f`. The conclusion is `Submonoid.FG` for the actual submonoid
of `T(F)/N`. Thus finitely many of its elements generate every quotient
class under multiplication and nonnegative integral powers.
The construction `CAplusQuotient` is the image in that ambient group
quotient of `CAplusMonoid F T R`, whose carrier is `CAplus F T R`.
Every class has a representative obtained by evaluating a cocharacter
nonnegative on `R` at the common chosen uniformizer. Equality of such
representatives in the quotient means that their ratio lies in `N`.
The compatible map `f` is supplied; its existence is not asserted.

This is a derived finite-generation replacement motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.2.5 (printed p.107 / PDF p.113) and V.3.23–V.3.24
(printed p.117 / PDF p.123), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source's `S` is the quotient of its nonnegative common-uniformizer
section by the section of the ambient group's split component. The
existing `CAplusQuotient` models precisely this ratio equivalence.
The printed assertion that `S` is a free monoid of rank the number of
simple roots fails in general, as recorded in the published integral
finite-generation statement's Markdown and issue I2 of the Chapter V
item ledger. This proposition asserts only finite generation.

The intended proof uses `IsSplitTorus.finite_simpleRelativeRoots` to obtain
finiteness of `R`, applies the published
`Langlands.GroupScheme.cocharacterConeFiniteGeneration` to the integral
quotient `CocharacterCone.quotient T R`, and transports finite generation
through the published monoid equivalence
`CocharacterUniformizer.coneQuotientComparison` at the same data.
The usual additive/multiplicative and submonoid/carrier finite-generation
equivalences supply the bookkeeping. None of these results is an extra
hypothesis of the proposition.

This file supplies a proposition definition and no proof. It asserts no
freeness, rank or generator count, no finite generation of the unquotiented
nonnegative section, and no strict-face partition.
