# Finite-index restriction of rational characters to a split component

Author: Worker 1292.

`Langlands.GroupScheme.CharacterRestrictionFiniteIndexStatement` is a
universe-polymorphic `Prop`-valued definition. It states the following
proposition, without proving it: over every field `k`, restriction of rational
characters of a connected reductive group `G` to any split component
`i : A.toGrp ⟶ G` has image of finite index in the character group of `A`.

## Hypotheses and objects

The universe `u` is arbitrary. The binders range over every `k : Type u` with
`[Field k]` and every `G : GroupScheme (Spec (CommRingCat.of k))`. The base
scheme is therefore `Spec k`. The field can be imperfect or have positive
characteristic; no splitness, local-field or algebraic-closedness condition
is imposed on `k` or `G`.

The hypothesis `IsConnectedReductive G` is exactly the published predicate
from [`Reductive.Basic`](../Reductive/Basic.md). Its fields say that the
structure morphism of `G` is smooth and affine, that the underlying scheme
is connected, and that the geometric unipotent radical is trivial. The last
condition is `HasTrivialUnipotentRadical` after base change along
`toAlgebraicClosure k`: every smooth connected normal unipotent closed
subgroup of that base change has trivial image as a subgroup functor.

The next binders range over every commutative group scheme
`A : CommGroupScheme (Spec (CommRingCat.of k))` and every group-scheme
homomorphism `i : A.toGrp ⟶ G`. Here `A.toGrp` forgets the bundled
commutativity. The hypothesis `IsSplitComponent i` is the published
predicate from [`Rational.Characters`](Characters.md). It says that `i` is
a central split torus and is maximal among central split tori through which
it factors. More explicitly:

- `IsSplitSubtorus i` says that `A` is a split torus and `i` is a closed
  immersion.
- `IsCentral i` means that all points of `A` map into the functorial centre
  of `G`: after every change of test scheme, their images commute with all
  points of `G`.
- If `i' : A'.toGrp ⟶ G` is another central split torus and
  `f : A.toGrp ⟶ A'.toGrp` satisfies `f ≫ i' = i`, then `IsIso f`.

This formulation uses the functorial centre and places no smoothness or
reducedness requirement on a scheme representing the centre. The statement
is conditional on the supplied split component; it does not assert its
existence.

## Restriction and the conclusion

The published `rationalCharacters G`, denoted `X^*(G)_k`, is
`HomAdd G (Gm (Spec (CommRingCat.of k))).toGrp`: group-scheme homomorphisms
from `G` to the multiplicative group over `k`, with pointwise multiplication
written additively. Thus zero is the constant character with value `1`.
For the commutative group scheme `A`, `rationalCharacters A.toGrp` is the
published character lattice `characterLattice A`, denoted `X^*(A)`.

The published additive homomorphism
`characterRestrict i : rationalCharacters G →+ rationalCharacters A.toGrp`
is precomposition with `i`: on underlying homomorphisms it sends `χ` to
`i ≫ χ.toMul`. Its range is the additive subgroup of characters of `A`
that extend to characters of `G`.

The conclusion is exactly `(characterRestrict i).range.FiniteIndex`.
Mathlib's `AddSubgroup.FiniteIndex` means that this additive subgroup has
finitely many cosets, or equivalently that the quotient of
`rationalCharacters A.toGrp` by the range is finite. Its defining field is
`index_ne_zero`, since Mathlib assigns index `0` to infinite index.

The binders and hypotheses agree with
[`CharacterRestrictionStatement`](CharactersStatement.md); the conclusion
is exactly its second conjunct. The first conjunct there asserts
injectivity. This separate target supports an independent proof of the
finite-index part while the combined statement retains both obligations.
Injectivity is neither assumed nor asserted here, and no consumer target
appears as a hypothesis.

## Source and derived provenance

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, content SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The relevant locations are:

- V.2.1, printed p.104 (PDF p.110), defines the split component of a
  reductive group as a maximal split torus in the centre.
- V.2.2, printed p.105 (PDF p.111), defines rational characters as the
  algebraic characters defined over the base field.
- V.2.6, opening on printed p.107 (PDF p.113), and the Lemme and its proof
  on printed p.108 (PDF p.114), consider restriction to the split
  component. The proof passes through the torus `G/𝒟G` and shows that the
  restriction image has finite index, as well as proving injectivity.

Renard works over a nonarchimedean local field `F`. The arbitrary-field
scope here is derived and matches the published
`CharacterRestrictionStatement`. A standard route to this generalization
uses a faithful finite-dimensional representation and its weight spaces
for the central split torus. Centrality makes those weight spaces
`G`-stable, and their determinant characters restrict to the corresponding
weights multiplied by their positive dimensions. Faithfulness ensures
that the occurring weights generate the torus's character lattice, so
these multiples generate a subgroup of finite index. This algebraic
route uses no local-field hypothesis. It explains the derived scope; the
Lean file only defines the proposition and contains no proof of it.
