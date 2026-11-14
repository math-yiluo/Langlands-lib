# Actual standard-Levi strict pieces in the common-uniformizer quotient

Author: Worker 1222.

`Langlands.GroupScheme.CocharacterUniformizer.standardLeviStrictQuotientFace`
defines the actual strict piece indexed by a set `J` of characters. Its
parameters are a nonarchimedean local field `F : Type u`, an actual commutative
group scheme `T`, an actual affine group scheme `G`, a morphism `i : T → G`,
a cocharacter `ν`, and an actual morphism `f₀ : A₀ → T` of commutative group
schemes. Put `N = f₀(C_{A₀})`, using the published common-uniformizer subgroup
and rational-point map. The resulting piece is a subset of the actual
rational-point quotient `T(F)/N`.

Membership first requires `J ⊆ simpleRelativeRoots i ν`. It then requires an
actual group scheme `L` and a closed inclusion `j : L → G` representing the
existing standard Levi functor for `J`, a split component `b : B → L`, and
an actual compatible morphism `g : B → T` with `g ≫ i = b ≫ j`. The quotient
class must be represented by `g(y)` for a point
`y ∈ CAstrict F B (restrictedSimpleCharacters i ν J g)`. Both the restricted
characters and the strict common-uniformizer section are the existing
constructions. All representatives, split components and compatible maps are
existentially quantified; no choice of a family is built into the definition.

The introduction theorem sends every strict point of any such actual
representative into this piece. Its proof supplies those objects and the
two image witnesses. An index not contained in the actual simple roots gives
the empty set, by the first membership condition.

The definition requires neither reductivity nor maximality, genericity,
splitness of `T`, or that `A₀` be an ambient split component. Those hypotheses
belong to the separate partition and comparison statements. In particular,
this file proves no existence of representative data, independence of their
images, nonnegative containment, covering, disjointness, integral comparison,
finite generation or freeness. Valid indices are allowed to have empty pieces
at this level.

This is a derived actual-object formulation of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.3.21, printed p.116 / PDF p.122, and V.3.23–V.3.24,
printed p.117 / PDF p.123, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.24 writes its strict piece as the quotient of the strict lattice cut
of a standard Levi split component by the ambient split-central uniformizer
subgroup. The present construction records its image in a single ambient
quotient. The use of all actual representatives is internal and preserves
the structural existence and image comparisons as separate obligations.
It makes no claim about the full rational-point cones of V.3.21.1 or the
source's general free-monoid assertion.
