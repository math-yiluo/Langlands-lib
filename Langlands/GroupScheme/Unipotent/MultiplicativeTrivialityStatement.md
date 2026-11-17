# Unipotent groups and groups of multiplicative type

`Langlands.GroupScheme.UnipotentMultiplicativeTrivialityStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

For every field `k : Type u`, the proposition is the conjunction of three
assertions about group schemes over `Spec (CommRingCat.of k)`.

1. (Milne 14.16.) If `G` satisfies `[LocallyOfFiniteType G.X.hom]` and
   `[IsAffineHom G.X.hom]`, and `IsMultiplicativeType G` and `IsUnipotent G`
   hold, then `SubgroupFunctor.range (𝟙 G) = ⊥`.
2. (Milne 14.17.) If `G` satisfies `[LocallyOfFiniteType G.X.hom]` and
   `[IsAffineHom G.X.hom]`, and `i : U ⟶ G`, `j : M ⟶ G` satisfy
   `IsClosedSubgroup i`, `IsClosedSubgroup j`, `IsUnipotent U` and
   `IsMultiplicativeType M`, then
   `SubgroupFunctor.range i ⊓ SubgroupFunctor.range j = ⊥`.
3. (Milne 14.18.) If `U` and `M` both satisfy `LocallyOfFiniteType` and
   `IsAffineHom` for their structure morphisms, `IsUnipotent U` and
   `IsMultiplicativeType M`, then `SubgroupFunctor.range f = ⊥` for every
   homomorphism `f : U ⟶ M` and for every homomorphism `f : M ⟶ U`.

The ingredients are existing declarations, used without change.

- `IsUnipotent` and `IsClosedSubgroup` (from
  [`Reductive.Basic`](../Reductive/Basic.md)). `IsUnipotent G` says that
  every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector. `IsClosedSubgroup i` says that the underlying
  morphism of schemes of the homomorphism `i` is a closed immersion.
- `IsMultiplicativeType` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that,
  after base change to some field extension `K` of `k`, `G` becomes
  isomorphic to the diagonalizable group `D(Λ)` of a finitely generated
  commutative group `Λ`.
- `SubgroupFunctor.range f` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  assigns to each scheme `T` over `Spec k` the subgroup of `T`-points of the
  target that factor through `f`. `⊓` is the pointwise intersection, and `⊥`
  assigns the trivial subgroup to every `T`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Proposition 14.16, p.284: "An algebraic group that is both multiplicative
  and unipotent is trivial."
- Corollary 14.17, p.284: "The intersection of a unipotent algebraic subgroup
  of an algebraic group with an algebraic subgroup of multiplicative type is
  trivial."
- Corollary 14.18, p.284: "There are no nontrivial homomorphisms over k
  (a) from a unipotent algebraic group to an algebraic group of
  multiplicative type, or (b) from an algebraic group of multiplicative type
  to a unipotent algebraic group."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative
  type if it becomes diagonalizable over some field containing k."
- p.7, before Definition 1.3: "An algebraic group G is trivial if e: ∗ → G is
  an isomorphism, and a homomorphism G → G′ is trivial if it factors through
  e′: ∗ → G′." Definition 1.3, p.7, defines an algebraic subgroup as a
  `k`-subscheme that is an algebraic group under the inclusion, and
  Proposition 1.41, p.18, says: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states 14.16, 14.17 and 14.18
on printed p.284 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.7, 135 or 236. Their p.18 entry concerns the
proof of 1.40, not Proposition 1.41. The 2022 errata add a sentence after
Definition 1.3: the identity section `e → G` factors through `H` and gives
`H` a neutral element. This does not change the definition.

Milne's proofs: for 14.16, a faithful representation of a group of
multiplicative type is a direct sum of simple representations (12.30), and
a unipotent group acts trivially on each simple representation, so the group
is trivial. 14.17 follows because both properties pass to algebraic
subgroups (12.9, 14.7). 14.18 follows because the image of such a
homomorphism is both unipotent and of multiplicative type (12.9, 14.7). This
is explanation only. The statement does not depend on that route.

## Derivation from the source

- **Algebraic groups.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 14 convention. The groups `G` in parts
  1 and 2 and the groups `U` and `M` in part 3 are assumed to satisfy
  `LocallyOfFiniteType` and `IsAffineHom`. An affine morphism is
  quasi-compact, so these groups are of finite type over `k`. In part 2 the
  subgroups `U` and `M` carry no such instances: they are closed subschemes
  of `G`, so they are affine and of finite type over `k` automatically.
- **Multiplicative and unipotent.** "Multiplicative" in 14.16 means "of
  multiplicative type" (Definition 12.17), which is `IsMultiplicativeType`;
  its comparison with Milne's definition is recorded in
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md). "Unipotent"
  is 6.45, which is `IsUnipotent`; its comparison is recorded in
  [`Reductive.Basic`](../Reductive/Basic.md).
- **Trivial group.** `SubgroupFunctor.range (𝟙 G) = ⊥` says that every point
  of `G` with values in any scheme over `k` is the identity. By the Yoneda
  lemma this says that `G` is the trivial group: its identity morphism
  factors through the identity section.
- **Algebraic subgroups and their intersection.** An algebraic subgroup of
  `G` is a closed subscheme that is a subgroup (Definition 1.3 and
  Proposition 1.41). Part 2 quantifies over homomorphisms `i : U ⟶ G` and
  `j : M ⟶ G` whose underlying morphisms are closed immersions, which
  identify `U` and `M` with algebraic subgroups of `G`. The intersection of
  the two subgroups is the fibre product `U ×_G M`. Its `T`-points are the
  `T`-points of `G` that factor through both `i` and `j`, which is
  `SubgroupFunctor.range i ⊓ SubgroupFunctor.range j`. So "the intersection
  is trivial" is that this subgroup functor is `⊥`.
- **Trivial homomorphisms.** A homomorphism `f` is trivial when it factors
  through the identity section of its target (p.7). By the Yoneda lemma this
  is `SubgroupFunctor.range f = ⊥`: every point of the target that factors
  through `f` is the identity.
- **Universes.** One universe `u` is used for `k` and all group schemes. This
  is a formalization convention.

## Related Library results

- `Langlands.GroupScheme.IsTorus.hom_eq_zero_of_isUnipotent` and
  `Langlands.GroupScheme.IsUnipotent.range_eq_bot_of_isTorus` (in
  [`Unipotent.TorusHom`](TorusHom.md)) prove the second half of part 3
  (Milne's 14.18(b)) when the source is a torus and the target is affine.
