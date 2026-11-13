# The nonnegative common-uniformizer monoid and its quotient image

Author: Worker 1222.

For any nonarchimedean local field `F : Type u`, actual commutative group
scheme `T` over `F`, and set `R` of actual characters of `T`,
`Langlands.GroupScheme.CocharacterUniformizer.CAplusMonoid F T R` is the
image of the published nonnegative integral cocharacter monoid under the
existing common-uniformizer section. Its multiplication is the actual
multiplication of `T(F)`. The theorem `mem_CAplusMonoid` proves that its
carrier is exactly the existing set `CAplus F T R`, defined by membership
in `C_T` and character norms at most one. The proof uses the published
section membership comparison in `CocharacterCone`; no splitness or
injectivity of the section is needed.

Given another actual commutative group scheme `A` and a morphism
`f : A → T`, let `N` be the image of `CA F A` in `T(F)`.
`CAplusQuotient F T R A f` is the submonoid image of `CAplusMonoid F T R`
under the actual group quotient map `T(F) → T(F)/N`.
`mem_CAplusQuotient` states that its elements are precisely classes with a
representative in the original `CAplus` set. Equality in this ambient
group quotient identifies two such representatives exactly when their
ratio lies in `N`. Thus the construction models the source's relation
quotient without making an arbitrary choice of representatives.

This is a derived construction motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.2.5 (printed p.107 / PDF p.113) and V.3.23–V.3.24
(printed p.117 / PDF p.123), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.2.5 uses one uniformizer to lift integral cocharacters, and V.3.24
forms the quotient of the nonnegative section by the section of the
ambient group's split component. Here arbitrary `A`, `T`, `f`, and `R`
are allowed; that generality and the use of the submonoid image in an
ambient group quotient are internal.

There are no reductivity, finite-character, characteristic, or positive-rank
restrictions. This module does not identify `N` with an integral root
annihilator, compare the quotient with the nonnegative cocharacter quotient,
assert finite generation or freeness, or decompose it into strict faces.
