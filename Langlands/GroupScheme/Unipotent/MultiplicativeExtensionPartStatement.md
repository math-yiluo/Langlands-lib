# The unipotent part of an extension of a multiplicative group

`Langlands.GroupScheme.MultiplicativeExtensionUnipotentPartStatement.{u}` is
a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. Let `U` and `M`
be group schemes over `Spec k` with homomorphisms `i : U ⟶ G` and
`q : G ⟶ M`, and assume the five hypotheses

- `IsClosedSubgroup i`, `IsUnipotent U`,
  `(SubgroupFunctor.range i).IsNormal`,
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`,
- `IsMultiplicativeType M`.

The conclusion is the conjunction of four parts.

1. **Smallest normal subgroup with multiplicative quotient.** For all group
   schemes `N` and `M'` over `Spec k` and homomorphisms `j : N ⟶ G` and
   `q' : G ⟶ M'` with `IsClosedSubgroup j`,
   `(SubgroupFunctor.range j).IsNormal`,
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q'` and
   `IsMultiplicativeType M'`,
   `SubgroupFunctor.range i ≤ SubgroupFunctor.range j`.
2. **Base change.** For every field `K : Type u` with `[Algebra k K]`, write
   `F` for the base-change functor
   `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
   Then `IsUnipotent (F.obj U)`, and for every group scheme `V` over
   `Spec K` and every homomorphism `j : V ⟶ F.obj G` with
   `IsClosedSubgroup j` and `IsUnipotent V`,
   `SubgroupFunctor.range j ≤ SubgroupFunctor.range (F.map i)`.
3. **Smoothness.** `Smooth G.X.hom → Smooth U.X.hom`.
4. **Connectedness.** `ConnectedSpace G.X.left → ConnectedSpace U.X.left`.

The ingredients are existing declarations, used without change.

- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`, on every
  test scheme over the base. `IsNormal` says that, on every test scheme,
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
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec K ⟶ Spec k`, as a functor; `F.map i`
  is the base-changed homomorphism `U_K ⟶ G_K`.
- `Smooth` (Mathlib) is smoothness of a morphism of schemes;
  `ConnectedSpace G.X.left` says that the underlying topological space of
  `G` is connected (in particular nonempty).

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Theorem 16.6(b), p.325: "G contains a normal unipotent algebraic subgroup
  G_u such that G/G_u is of multiplicative type." Notation 16.7, p.326:
  "When G is an algebraic group, we use G_u exclusively to denote a normal
  algebraic subgroup such that G_u is unipotent and G/G_u is of
  multiplicative type."
- Notes, p.326: "Let G be an algebraic group over k satisfying the
  equivalent conditions of Theorem 16.6."
- Note 16.8, p.326: "The algebraic subgroup G_u is characterized by each of
  the following properties: (a) it is the largest unipotent algebraic
  subgroup of G; (b) it is a normal unipotent algebraic subgroup U of G such
  that G/U is of multiplicative type; (c) it is the smallest normal
  algebraic subgroup U such that G/U is of multiplicative type. From (b), it
  follows that the formation of G_u commutes with extension of the base
  field."
- Note 16.10, p.326: "If G is smooth (resp. connected), then G_u is smooth
  (resp. connected) because it becomes a quotient of G over k^a (see 16.26a
  below)."
- Theorem 16.26, p.332: "Let G be a trigonalizable algebraic group over a
  field k. The extension e → G_u → G → D → e splits in each of the following
  cases: (a) the field k is algebraically closed; ..."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Definition 1.51(a), p.21: "An algebraic subgroup H of G is normal if
  H(R) is normal in G(R) for all small k-algebras R."
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative
  type if it becomes diagonalizable over some field containing k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map
  if it is faithfully flat." and "Thus a homomorphism is a quotient map if it
  is both flat and surjective."
- After Theorem 5.13, p.101: "It follows that a quotient map q: G → Q is
  uniquely determined by its kernel N up to a unique isomorphism. We denote
  any such map by q: G → G/N and call G/N the quotient of G by N."
  Theorem 5.14, p.102: "Every normal algebraic subgroup N of an algebraic
  group G arises as the kernel of a quotient map G → Q."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Notes 16.8 and 16.10
on printed p.326 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.99, 101, 102,
135, 236, 325, 326 or 332. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.21 entry concerns
Definition 1.48, not Definition 1.51. Their p.324 entry replaces
"diagonalizable" with "trigonalizable" in the last sentence of the first
paragraph of Chapter 16; it does not concern the affineness sentence. The
2022 errata have no entry for pp.21, 99, 101, 102, 135, 236, 324, 325, 326
or 332; their p.18 entry concerns the proof of Proposition 1.37.

Milne's arguments, for orientation only (the statement does not depend on
this route). For part 1, if `N` is normal with `G/N` of multiplicative type,
the composite `G_u → G → G/N` is trivial because homomorphisms from unipotent
groups to groups of multiplicative type are trivial (14.18, as in the proof
of Theorem 16.6), so `G_u ⊂ N`. For part 2, the conditions of 16.8(b) are
preserved by extension of the base field: `(G_u)_K` is unipotent (14.9),
normal, and `G_K/(G_u)_K = (G/G_u)_K` is of multiplicative type; so
`(G_u)_K` is the largest unipotent subgroup of `G_K` by 16.8(a). For parts 3
and 4, over `k^a` the group becomes trigonalizable and the extension
`e → G_u → G → D → e` splits (16.26(a)), so `(G_u)_{k^a}` is a quotient of
`G_{k^a}`.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 16 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **The hypotheses.** "`G` satisfies the equivalent conditions of
  Theorem 16.6", with `G_u` as in Notation 16.7, is condition 16.6(b) with
  its subgroup named: a normal unipotent algebraic subgroup `U = G_u` (a
  closed subgroup by Proposition 1.41) such that `G/U` is of multiplicative
  type. Milne tests normality on points with values in every `k`-algebra
  (Definition 1.51); `IsNormal` tests every scheme over `Spec k`, which gives
  the same condition because `U` is closed in `G` and membership of a point
  in `U` can be checked on an affine open cover of the test scheme. The
  quotient `G/U` exists (Theorem 5.14) and is determined by the kernel of the
  quotient map up to unique isomorphism (after Theorem 5.13), so "`G/U` is of
  multiplicative type" means that there is a quotient map `q : G ⟶ M` with
  kernel `U` and `M` of multiplicative type (Definition 12.17, with
  Theorem 12.8, p.233, for the finitely generated character group). Milne's
  quotient map is flat and surjective (Definition 5.5); `IsFppfQuotient`
  also asks that `q` be locally of finite presentation, which holds
  automatically because `G` and `M` are of finite type over a field.
- **Part 1 (Note 16.8(c)).** "The smallest normal algebraic subgroup `N`
  such that `G/N` is of multiplicative type" is stated as: `U` is contained
  in every normal closed subgroup `N` admitting a quotient map onto a group
  of multiplicative type with kernel `N`. Since `U` itself is such a
  subgroup, this says that `U` is the smallest one.
- **Part 2 (formation commutes with field extension).** By Note 16.8(a),
  `(G_K)_u` is the largest unipotent algebraic subgroup of `G_K`. The claim
  `(G_K)_u = (G_u)_K` is stated as: `(G_u)_K` is unipotent and contains every
  unipotent closed subgroup of `G_K`. The field `K` ranges over all field
  extensions of `k` in the universe `u`. The unipotence of `U_K` alone also
  follows from the Library statement `UnipotentFieldExtensionStatement`
  (Milne 14.9), since `U` is affine and of finite type.
- **Parts 3 and 4 (Note 16.10).** Smoothness of the algebraic group `G` over
  `k` is smoothness of the structure morphism `G → Spec k`, and connectedness
  is connectedness of the underlying topological space.
- **Not included.** Note 16.8(a) (largest unipotent subgroup of `G`) and the
  uniqueness of `G_u` are the last sentence of Theorem 16.6 and are not
  restated here, except over every extension `K` in part 2. Note 16.9
  (perfect fields, unipotent elements) is not part of this statement.
- **Universes.** One universe `u` is used for the fields, the groups in
  `IsMultiplicativeType` and the schemes. This is a formalization
  convention.
