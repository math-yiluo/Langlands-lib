# The nonnegative cocharacter and actual split-central quotients

Author: Worker 1222.

`Langlands.GroupScheme.CocharacterUniformizer.ConeQuotientComparisonStatement`
compares two actual monoids over any nonarchimedean local field `F : Type u`.
Let `G` be a connected reductive group scheme over `F`, let `i : T → G`
be a maximal split torus, and let `ν` be generic for the actual relative
roots. Let `a : A → G` be a split component, and supply any actual
commutative-group-scheme morphism `f : A → T` for which
`CommGroupScheme.groupHom f ≫ i = a`. Put `R = simpleRelativeRoots i ν`,
the actual simple relative roots, and let `P` be their common integral
annihilator in the actual cocharacter lattice of `T`.

The source monoid is the existing `CocharacterCone.quotient T R`, the
image of the nonnegative integral cocharacters in the quotient lattice
by `P`. Its addition is written multiplicatively using `Multiplicative`.
Let `N` be the image of the existing common-uniformizer subgroup `CA F A`
under `f` on rational points. The target monoid is
`CAplusQuotient F T R A f`, the actual image of the nonnegative section
`C_T^+` in `T(F)/N`. Its carrier and representative membership are specified
by `CocharacterUniformizerCone`.

The proposition asserts a multiplicative monoid isomorphism between these
monoids. For every nonnegative integral cocharacter `c`, it must take the
class of `c` to the rational-point quotient class of `c(π)`, for the same
chosen uniformizer used throughout the existing section constructions.
The formula uses all nonnegative representatives and does not choose a
generating set. The statement includes either field characteristic,
non-split reductive groups, nonreduced relative root systems and rank
zero. The compatible factorization `f` is supplied; its existence is not
asserted. This file states the proposition and supplies no proof.

This is a derived comparison motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.2.5 (printed p.107 / PDF p.113) and V.3.23–V.3.24
(printed p.117 / PDF p.123), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.24 defines its quotient using ratios in the split component's
common-uniformizer subgroup. The present statement identifies that
quotient with its integral nonnegative lattice model. Its explicit
actual-group-scheme formulation and use of the given generic cocharacter
and compatible `f` are internal.

The intended proof combines the existing simple-root integral
split-central-image statement and uniformizer group-quotient statement,
then restricts to the published nonnegative cone and the actual
nonnegative section. The group equivalence's representative formula and
the cone membership laws identify these submonoids.
Finite generation of either monoid, the source's false general freeness
assertion, and the strict-face decomposition are not part of this statement.
