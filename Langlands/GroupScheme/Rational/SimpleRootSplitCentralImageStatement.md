# Integral simple-root annihilators and actual split components

Author: Worker 1222.

`Langlands.GroupScheme.SimpleRootSplitCentralImageStatement` asserts the
following equality of integer submodules of the actual cocharacter lattice.
Let `G` be a connected reductive group scheme over any field `k : Type u`,
let `i : T → G` be an actual maximal split torus, and let `ν` be generic for
its actual relative roots. Let `a : A → G` be an actual split component of
`G`. For every actual morphism `f : A → T` satisfying
`CommGroupScheme.groupHom f ≫ i = a`, the common integral annihilator of
`simpleRelativeRoots i ν` equals the range of the published integral
postcomposition map `RealTorusSpace.cocharacterMapInt f`.

All objects and predicates are those of the shared group-scheme framework.
In particular the simple roots are defined from the actual Lie weights,
positivity is determined by `ν`, and the annihilator uses the actual integer
character–cocharacter pairing. The equality is integral, not just an equality
after extension to the real numbers. The statement includes arbitrary field
characteristic, non-split reductive groups, nonreduced relative root systems
and rank zero. It assumes neither a root-system realization nor linear
independence or freeness of a dominant monoid. The compatible factorization
`f` is given; this statement does not assert its existence.

This is a derived comparison motivated by David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026,
V.3.23–V.3.24, printed p.117 / PDF p.123, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
That passage uses the quotient of the nonnegative uniformizer lattice of a
maximal split torus by the uniformizer lattice of the split component of
`G`. V.2.5, printed p.107 / PDF p.113, identifies each split-torus
uniformizer lattice with its integral cocharacters and records compatibility
with split subtori. V.3.7, printed p.111 / PDF p.117, describes the real root
span complementary to the central directions. The present equality gives
the integral kernel comparison needed to connect those constructions;
its arbitrary-field formulation and chosen generic cocharacter are internal
generalizations, not a literal restatement of a numbered source assertion.

The intended proof reuses the published additive-group generation of all
relative roots by the simple roots under genericity and negation stability.
The published reductive relative-root negation theorem provides that
stability. Vanishing on the simple roots then implies vanishing on every
relative root, and the published root-annihilator centrality theorem makes
the cocharacter central on every test scheme. The published
`IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters` factors
precisely these integral cocharacters through `A`. Conversely, central
split-torus restriction makes each actual root vanish on the image of `A`,
so every integral cocharacter in that image lies in the common annihilator.
This file states the proposition and supplies no proof.

The uniformizer realization and quotient comparison, finite generation of
the nonnegative quotient, and its decomposition into strict faces remain
separate obligations. In particular this statement does not assert the
source's false general claim that the dominant quotient is a free monoid.
