# Groups that become trigonalizable over a separable extension

`Langlands.GroupScheme.SeparablyTrigonalizableCriterionStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. The statement
is the conjunction of two parts.

1. **(a) ⇔ (b).** The following are equivalent:
   - (a) there are a field `K : Type u` and `[Algebra k K]` with
     `Algebra.IsSeparable k K` and `IsTrigonalizable G_K`, where `G_K` is
     `(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`;
   - (b) there are group schemes `U` and `M` over `Spec k` and homomorphisms
     `i : U ⟶ G` and `q : G ⟶ M` such that `IsClosedSubgroup i`,
     `IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal`,
     `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` and
     `IsMultiplicativeType M`.
2. **Largest unipotent subgroup.** For all `U`, `M`, `i : U ⟶ G` and
   `q : G ⟶ M` satisfying the five conditions of (b), and for every group
   scheme `V` over `Spec k` and every homomorphism `j : V ⟶ G` with
   `IsClosedSubgroup j` and `IsUnipotent V`,
   `SubgroupFunctor.range j ≤ SubgroupFunctor.range i`.

The ingredients are existing declarations, used without change.

- `IsTrigonalizable` (from [`Trigonalizable`](../Trigonalizable.md)) says
  that every nonzero finite-dimensional matrix representation has a nonzero
  coordinate vector spanning a stable line: every point of the group, with
  values in any scheme over the base, maps it to a multiple of itself. This
  is Milne's Definition 16.1, as recorded in that module. For `G_K` the
  field is `K`.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec K ⟶ Spec k`.
- `Algebra.IsSeparable k K` (Mathlib) says that every element of `K` is
  separable over `k`: its minimal polynomial over `k` is separable. The zero
  polynomial is not separable, so every element is algebraic over `k`.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme over `Spec k`. `IsNormal` says that, on every test scheme,
  these points form a normal subgroup of the points of `G`. The order `≤`
  is inclusion of these subgroups on every test scheme.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.
- `IsMultiplicativeType M` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that
  there are a field extension `L : Type u` of `k` and a finitely generated
  commutative group `Λ : Type u` such that `M_L` is isomorphic, as a group
  scheme, to the diagonalizable group `D(Λ)` over `L`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.6, pp.325–326: "The following conditions on an algebraic group
  G over k are equivalent: (a) G becomes trigonalizable over a separable
  field extension of k; (b) G contains a normal unipotent algebraic subgroup
  G_u such that G/G_u is of multiplicative type. When these conditions
  hold, G_u is unique and contains every unipotent algebraic subgroup of G."
- Notations, p.3: "a separable extension is a separable algebraic
  extension."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative
  type if it becomes diagonalizable over some field containing k."
- Definition 1.51(a), p.21: "An algebraic subgroup H of G is normal if
  H(R) is normal in G(R) for all small k-algebras R."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map
  if it is faithfully flat." and "Thus a homomorphism is a quotient map if it
  is both flat and surjective."
- After Theorem 5.13, p.101: "It follows that a quotient map q: G → Q is
  uniquely determined by its kernel N up to a unique isomorphism. We denote
  any such map by q: G → G/N and call G/N the quotient of G by N."
  Theorem 5.14, p.102: "Every normal algebraic subgroup N of an algebraic
  group G arises as the kernel of a quotient map G → Q."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Theorem 16.6 on
printed pp.325–326 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.3, 99, 101,
102, 233, 236, 325 or 326. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.21 entry concerns
Definition 1.48, not Definition 1.51. Their p.324 entry replaces
"diagonalizable" with "trigonalizable" in the last sentence of the first
paragraph of Chapter 16; it does not concern the affineness sentence. The
2022 errata have no entry for pp.324, 325 or 326.

Milne's proof, for orientation only (the statement does not depend on this
route). A normal unipotent subgroup `U` with `G/U` of multiplicative type
contains every unipotent subgroup `V`, because the composite `V → G → G/U`
is trivial (14.18); so there is at most one such `U`. (a)⇒(b): over a
finite Galois extension `k'` with `G_k'` trigonalizable, Proposition 16.2(d)
gives such a subgroup of `G_k'`; being unique, it is stable under
`Gal(k'/k)` and so comes from an algebraic subgroup of `G` (1.54). (b)⇒(a):
`G/G_u` becomes diagonalizable over a finite separable extension `k'`
(12.18), `G_u` remains unipotent over `k'` (14.9), and Proposition 16.2(d)
applies.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **(a): separable field extension.** By Milne's convention on p.3, a
  separable field extension of `k` is a separable algebraic extension. This
  is a field `K` with an algebra structure over `k` and
  `Algebra.IsSeparable k K`, which includes algebraicity. "`G` becomes
  trigonalizable over `K`" is `IsTrigonalizable G_K` for the base change
  `G_K`. The field `K` lies in the universe `u` of `k`. This loses nothing:
  every algebraic extension of `k` embeds into `AlgebraicClosure k`, which
  lies in that universe.
- **(b): the subgroup.** A normal unipotent algebraic subgroup is a group
  scheme `U` with a homomorphism `i : U ⟶ G` that is a closed immersion
  (Proposition 1.41), with `IsUnipotent U` and normal range. Milne tests
  normality on points with values in every `k`-algebra (Definition 1.51).
  The Library predicate `IsNormal` tests every scheme over `Spec k`. The two
  agree because `U` is closed in `G`: membership of a point in `U` and the
  conjugation identities can be checked on an affine open cover of the test
  scheme.
- **(b): the quotient.** The quotient `G/U` exists (Theorem 5.14) and is
  determined by the kernel of the quotient map up to unique isomorphism
  (after Theorem 5.13). So "`G/U` is of multiplicative type" means that
  there is a quotient map `q : G ⟶ M` with kernel `U` and `M` of
  multiplicative type. Milne's quotient map is a flat surjective
  homomorphism (Definition 5.5). `IsFppfQuotient` also asks that `q` be
  locally of finite presentation; this holds automatically because `G` and
  `M` are of finite type over a field (see the next item). Its kernel clause
  says that the actual kernel of `q` has the same points as `U` on every
  test scheme. Since `i` and `kernelι q` are monomorphisms, this identifies
  the kernel with `U` as subgroup schemes of `G`.
- **(b): multiplicative type.** Milne's Definition 12.17 is "diagonalizable
  over some field containing `k`". By Theorem 12.8 (p.233), a diagonalizable
  algebraic group is isomorphic to `D(Λ)` for a commutative group `Λ`,
  finitely generated because `D(Λ)` is of finite type. This is
  `IsMultiplicativeType M`. No hypothesis on `M` is imposed beyond this:
  `M_L ≅ D(Λ)` is affine and of finite type over `L`, and both properties
  descend along the faithfully flat quasi-compact morphism
  `Spec L ⟶ Spec k`. So `M` is an affine algebraic group, as Milne's
  convention requires.
- **Largest unipotent subgroup.** "Contains every unipotent algebraic
  subgroup" says that for every closed subgroup `j : V ⟶ G` with `V`
  unipotent, every point of `G` factoring through `V` factors through `U`,
  on every test scheme. This is `range j ≤ range i`. The clause is stated
  for every `U`, `M`, `i`, `q` satisfying the conditions of (b), which is
  how Milne's proof establishes it. Uniqueness of `G_u` is not stated
  separately. It follows from the clause: if `(U, i)` and `(U', i')` both
  satisfy (b), each is a closed unipotent subgroup, so their ranges contain
  each other.
- **Universes.** One universe `u` is used for the fields, the groups in
  `IsMultiplicativeType` and the schemes. This is a formalization
  convention.
