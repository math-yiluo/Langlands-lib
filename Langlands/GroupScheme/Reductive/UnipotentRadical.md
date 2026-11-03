# Represented ground-field unipotent radicals

This module defines predicates on actual homomorphisms of the Library's group
schemes over `Spec (CommRingCat.of k)`, for every field `k : Type u` and arbitrary
universe `u`. It characterizes a representative when supplied; it constructs no
radical and asserts no existence theorem. The ambient group need not satisfy a
smoothness, connectedness or affineness hypothesis for the predicates to be
well-formed. Their intended algebraic-group application is to smooth affine
groups, as in the source.

## Source and correspondence

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`.

- Definition 1.1.1, printed p.3, defines the ground-field unipotent radical
  using smoothness, connectedness, unipotence and normality over `k`.
- The discussion before Proposition 2.2.4, printed p.63, specifies the split
  ground-field radical by adding splitness.
- Theorem B.3.4 and Corollary B.3.5, printed pp.573–574, discuss the split part
  of a smooth connected unipotent group and identify the split radical with the
  split part of the ground-field radical. These are separate structural results,
  not hypotheses or conclusions of this module.

CGP uses maximality for these canonical radicals. Here it is expressed explicitly
as greatest-subgroup containment: the supplied representative contains every
subgroup in the defining class. This avoids the weaker condition that there is
merely no strictly larger candidate. In CGP's smooth affine setting it is the
greatest radical of Definition 1.1.1; its existence is not proved here.

## Definitions

`IsUnipotentRadical (i : U ⟶ G)` is a proposition with the following fields:

- `isClosedSubgroup`: the underlying scheme map is a closed immersion, using the
  existing `IsClosedSubgroup`;
- `smooth`, `connectedSpace`, `isUnipotent`: `U` is smooth over `k`, its underlying
  topological space is connected, and it satisfies the existing `IsUnipotent`;
- `isNormal`: the existing `SubgroupFunctor.range i` is normal on every test;
- `greatest`: for every ground-field group scheme `H` and homomorphism `j : H ⟶ G`
  with these same five properties, `SubgroupFunctor.range j ≤ SubgroupFunctor.range i`.

The last inclusion is tested on every relative scheme `T`, and says that every
`T`-point of `G` factoring through `j` also factors through `i`. Both nonaffine
and nonreduced schemes are included. Neither containment nor normality is
defined solely by rational points.

`IsSplitUnipotentRadical i` has these same five subgroup properties and the
additional field `isSplitUnipotent : RelativeRoot.IsSplitUnipotent U`. Its
`greatest` field quantifies only over competitors that also satisfy this split
predicate. It reuses, without an adapter or a second notion of splitness,
`RelativeRoot.IsSplitUnipotent` from
`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`: a finite normal
series with smooth connected closed kernels, represented fppf quotients having
the all-test functor of the one-dimensional additive group, and a trivial
endpoint. Importing that module uses its definitions; none of its separate
structural proposition targets is assumed proved.

Three notions remain distinct over imperfect fields:

1. `R_{u,k}(G)` is the greatest ground-field radical characterized here.
2. `R_{us,k}(G)` is the greatest split ground-field radical, using the narrower
   class of split competitors.
3. The geometric radical belongs to the base change of `G` to an algebraic
   closure, not to `G` over `k`. It can be characterized by applying
   `IsUnipotentRadical` to a homomorphism over that algebraic closure.

The module makes no identification between the ground-field radical after base
change and the geometric radical, and does not require a ground-field radical
to be split. CGP's discussion on printed pp.4–5 explains why the ground-field
and geometric notions differ over imperfect fields. The existing
`IsConnectedReductive` continues to test radical triviality after algebraic
closure; `IsPseudoReductive` continues to test it over the ground field.

## Proved elementary consequences

These laws are proved from the definitions, without a radical-existence result:

- `IsUnipotentRadical.range_eq` and `IsSplitUnipotentRadical.range_eq` prove
  equality of any two represented radicals' all-test images, in the respective
  class. Each greatest field gives one inclusion; antisymmetry gives equality.
  No chosen isomorphism of representatives is asserted.
- `IsUnipotentRadical.range_eq_bot` and
  `IsSplitUnipotentRadical.range_eq_bot` apply the existing
  `HasTrivialUnipotentRadical G` to the supplied representative.
- `IsUnipotentRadical.hasTrivialUnipotentRadical_iff` identifies that existing
  triviality predicate with triviality of a supplied ground-field radical's
  image. For the reverse implication, greatestness puts every competitor's
  image in the trivial image, and pointwise subgroup antisymmetry gives equality
  with the identity functor.
- `IsUnipotentRadical.isSplitUnipotentRadical` restricts greatestness to split
  competitors when the supplied radical itself is split.
- `IsSplitUnipotentRadical.range_le_unipotentRadical` puts a supplied split
  radical in any supplied ground-field radical by the latter's greatest field.

The corresponding converse from a trivial split radical to a trivial
ground-field radical is not asserted. Quotient geometry, compatibility with
field extensions, characteristic invariance, and existence of the radicals
remain separate obligations.
