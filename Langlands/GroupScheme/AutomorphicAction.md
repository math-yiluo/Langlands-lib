# Automorphic group-scheme actions and all-test fixed subgroups

Let `H` and `G` be actual group schemes over an arbitrary scheme `S`, in the
Library category `GroupScheme S = Grp (Over S)`. This module constructs actions
of `H` on `G` by group automorphisms and their fixed subgroup functors.

## Sources and intrinsic extension

Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §2.1
introduction, printed p.45 / PDF p.71, and Remark 2.1.11, printed p.59 / PDF p.85,
use abstract left actions by group automorphisms. Proposition A.8.10(1),
printed pp.547–548 / PDF pp.573–574, describes the invariant locus by requiring
the base-changed acting group to act trivially on the point. The source is
registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

Those source constructions are phrased over an affine base and on algebra
points. Here the elementary action data and fixed-point condition are extended
intrinsically to every scheme over any base `S`. A single morphism in `Over S`
induces the point maps by composition with product pairings; associativity of
composition proves their naturality. The laws are required on every test
scheme, and the fixed condition quantifies over every further test refinement.
Thus neither affine tests nor rational points alone are substituted for the
scheme-theoretic action or invariant condition.

The bundling, elementary consequences and comparisons below are derived
constructions, using the published `SubgroupFunctor`, `NormalizedSubgroup`
and `torusCentralizer` APIs. They do not use the representability theorem of
Proposition A.8.10, nor its separatedness, flatness or local projectivity
hypotheses.

## Action data and point automorphisms

All new declarations are in `Langlands.GroupScheme` or its namespace
`AutomorphicAction`.

`AutomorphicAction H G` has one underlying morphism
`hom : H.X ⊗ G.X ⟶ G.X` and precisely three intrinsic laws, on every
`T : Over S`: the identity of `H(T)` acts trivially, a product in `H(T)` acts
by successive actions, and every acting point preserves multiplication in
`G(T)`. These are laws of the morphism's induced point maps.

`act h g` is `lift h g ≫ hom`; `act_eq` states that formula.
`act_one_left`, `act_mul_left` and `act_mul_right` expose the three laws.
`naturality` states
`b ≫ act h g = act (b ≫ h) (b ≫ g)` for every test morphism `b`.

`pointAut T h` packages the action as a multiplicative automorphism of `G(T)`.
Its inverse is the action of `h⁻¹`: the two inverse identities follow by the
left multiplication law and the left identity law. `pointsAction T` packages
these automorphisms as a homomorphism `H(T) →* MulAut G(T)`, and
`pointsAction_apply` identifies its application with `act`.
Preservation of the identity and inverse in `G(T)` is derived from this
automorphism in `act_one` and `act_inv`. `act_inv_act` and `act_act_inv`
give the two cancellation identities.

`restrict a f`, for an actual group-scheme homomorphism `f : K ⟶ H`,
precomposes `a.hom` with `f × id`. The homomorphism laws of `f` give the
three action laws. `restrict_act` proves its point formula
`(a.restrict f).act k g = a.act (k ≫ f.hom.hom) g`.

## Fixed subgroup functor

`IsFixed a g` requires that for every `T' : Over S`, every morphism
`b : T' ⟶ T` and every `h : T' ⟶ H.X`, one has
`a.act h (b ≫ g) = b ≫ g`. In particular, this is stronger than merely testing
the acting points over `T`.

`isFixed_iff_universal` proves equivalence with the single equation
`a.act (snd T H.X) (fst T H.X ≫ g) = fst T H.X ≫ g` on `T ×_S H`.
The forward implication specializes the refinements to the two projections.
The reverse implication pulls the universal equation back along `lift b h`
and uses naturality and the projection equations.

`fixedSubgroup a` is the resulting `SubgroupFunctor G`.
Preservation of identity, products and inverses by the action proves its
subgroup laws. Composing test refinements proves stability under every
restriction. `mem_fixedSubgroup` exposes the all-refinement definition;
`mem_fixedSubgroup_iff_universal` exposes the universal equation.
Nonreduced tests and nonsmooth acting groups are included.

## Conjugation comparisons

For homomorphisms `iG : G ⟶ A` and `iH : H ⟶ A`, assume that
`SubgroupFunctor.range iG` is normalized by `SubgroupFunctor.range iH`,
and that the underlying morphism of `iG` in `Over S` is a monomorphism.
`ofNormalizedConjugation iG iH hn` bundles exactly the existing morphism
`SubgroupFunctor.normalizedConjugation iG iH hn`, using its published three
action laws. `ofNormalizedConjugation_pointsAction` proves equality with the
published `SubgroupFunctor.normalizedConjAction` on each test scheme.

`range_id_isNormalizedBy` observes that the whole ambient group is normalized
by every image. Applying the preceding adapter with `iG = id` defines
`conjugation i : AutomorphicAction H G` for every `i : H ⟶ G`.
`conjugation_act` proves
`(conjugation i).act h g = i(h) * g * i(h)⁻¹` using the published normalized
conjugation formula. No parallel conjugation construction or proof of its
action laws is introduced.

For `C : CommGroupScheme S` and any `i : C.toGrp ⟶ G`,
`conjugation_fixedSubgroup_eq_torusCentralizer` proves that the fixed functor
equals `torusCentralizer i`. On every refinement, the equation
`i(h) * g * i(h)⁻¹ = g` is equivalent to commutation. The commutativity
assumption here accommodates the existing `torusCentralizer` interface;
no torus, smoothness, reducedness or affineness hypothesis is added.

This module constructs subgroup functors and their elementary laws.
Representability, quotient-action descent and relative root groups are not
consequences asserted by these declarations.
