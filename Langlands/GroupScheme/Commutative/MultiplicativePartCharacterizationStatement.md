# The multiplicative part of a commutative algebraic group

`Langlands.GroupScheme.CommutativeMultiplicativePartCharacterizationStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]`, `[IsAffineHom G.X.hom]` and
`[IsCommMonObj G.X]`. Let `S` and `Q` be group schemes over `Spec k` with
homomorphisms `s : S ⟶ G` and `q : G ⟶ Q`, and assume the four hypotheses
`IsClosedSubgroup s`, `IsMultiplicativeType S`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q` and
`IsUnipotent Q`. The conclusion is the conjunction of five parts.

1. **Largest subgroup of multiplicative type.** For every group scheme `H`
   over `Spec k` and every homomorphism `h : H ⟶ G` with
   `IsClosedSubgroup h` and `IsMultiplicativeType H`,
   `SubgroupFunctor.range h ≤ SubgroupFunctor.range s`.
2. **Smallest subgroup with unipotent quotient.** For all group schemes `H`
   and `Q'` over `Spec k` and homomorphisms `h : H ⟶ G` and `q' : G ⟶ Q'`
   with `IsClosedSubgroup h`,
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q'` and
   `IsUnipotent Q'`, `SubgroupFunctor.range s ≤ SubgroupFunctor.range h`.
3. **Base change.** For every field `K : Type u` with `[Algebra k K]`, write
   `F` for the base-change functor
   `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
   Then `IsMultiplicativeType (F.obj S)`, and for every group scheme `H` over
   `Spec K` and every homomorphism `h : H ⟶ F.obj G` with
   `IsClosedSubgroup h` and `IsMultiplicativeType H`,
   `SubgroupFunctor.range h ≤ SubgroupFunctor.range (F.map s)`.
4. **Smoothness.** `Smooth G.X.hom → Smooth S.X.hom`.
5. **Connectedness.** `ConnectedSpace G.X.left → ConnectedSpace S.X.left`.

The ingredients are existing declarations, used without change.

- `IsCommMonObj G.X` (Mathlib) says that the multiplication of the group
  object `G.X` is commutative.
- `IsClosedSubgroup s` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `s` is a closed immersion.
  `IsUnipotent Q` (same module) says that every nonzero finite-dimensional
  matrix representation of `Q` has a nonzero fixed vector (Milne 6.45).
- `IsMultiplicativeType S` (from
  [`Torus.MultiplicativeType`](../Torus/MultiplicativeType.md)) says that
  there are a field extension `L : Type u` of `k` and a finitely generated
  commutative group `Λ : Type u` such that `S_L` is isomorphic, as a group
  scheme, to the diagonalizable group `D(Λ)` over `L`.
- `SubgroupFunctor.range s` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `s`, on every
  test scheme over the base. The order `≤` is inclusion of these subgroups
  on every test scheme.
- `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of schemes of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme kernel `kernelι q` (from
  [`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) equals `N` on
  every test scheme.
- `GroupScheme.baseChange` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is base
  change of group schemes along `Spec K ⟶ Spec k`, as a functor; `F.map s`
  is the base-changed homomorphism `S_K ⟶ G_K`.
- `Smooth` (Mathlib) is smoothness of a morphism of schemes;
  `ConnectedSpace S.X.left` says that the underlying topological space of
  `S` is connected (in particular nonempty).

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Note 16.17, p.329: "Let G be a commutative algebraic group over k. The
  algebraic subgroup G_s of G in Theorem 16.13 is characterized by each of
  the following properties: (a) it is the largest algebraic subgroup of G of
  multiplicative type; (b) it is an algebraic subgroup H of G of
  multiplicative type such that G/H is unipotent; (c) it is the smallest
  algebraic subgroup H of G such that G/H is unipotent. It follows from (b)
  that the formation of G_s commutes with extension of the base field."
- After the proof of Theorem 16.13, p.329: "Because G_s and G_u become
  quotients of G over k^a, they are smooth or connected if G is smooth or
  connected."
- Theorem 16.13(a), p.328: "There exists a largest algebraic subgroup G_s of
  G of multiplicative type; this is a characteristic subgroup of G, and the
  quotient G/G_s is unipotent."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
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
one-based PDF page is the printed page plus 11) states Note 16.17 and the
remark after the proof of Theorem 16.13 on printed p.329 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.99, 101, 102,
135, 236, 328 or 329. Their p.18 entry concerns the proof of
Proposition 1.40, not Proposition 1.41. Their p.324 entry replaces
"diagonalizable" with "trigonalizable" in the last sentence of the first
paragraph of Chapter 16; it does not concern the affineness sentence. The
2022 errata have no entry for pp.99, 101, 102, 135, 236, 324, 328 or 329;
their p.18 entry concerns the proof of Proposition 1.37.

Milne gives no separate proof of Note 16.17. For orientation only (the
statement does not depend on this route): homomorphisms from groups of
multiplicative type to unipotent groups are trivial (14.17, 14.18). So a
subgroup `H` of multiplicative type maps trivially to `G/S` and lies in `S`
(part 1), and `S` maps trivially to `G/H` when `G/H` is unipotent and lies in
`H` (part 2). The conditions of part (b) survive base change, which gives
part 3 by part 1 over `K`. For parts 4 and 5, Milne's remark uses that over
`k^a` the group `G` is the product `G_u × G_s` (Theorem 16.13(b)), so that
`G_s` becomes a quotient of `G`.

## Derivation from the source

- **Commutative algebraic group.** Milne's algebraic group is a group scheme
  of finite type over `k`, affine by the Chapter 16 convention. The
  statement assumes `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`;
  an affine morphism is quasi-compact, so `G` is of finite type over `k`.
  Commutativity is `IsCommMonObj G.X`.
- **The hypotheses (property 16.17(b)).** An algebraic subgroup is a group
  scheme with a homomorphism to `G` that is a closed immersion
  (Proposition 1.41). Every subgroup of the commutative group `G` is normal,
  so the quotient `G/S` exists (Theorem 5.14) and is determined by the kernel
  of the quotient map up to unique isomorphism (after Theorem 5.13). "`G/S`
  is unipotent" means that there is a quotient map `q : G ⟶ Q` with kernel
  `S` and `Q` unipotent. Milne's quotient map is flat and surjective
  (Definition 5.5); `IsFppfQuotient` also asks that `q` be locally of finite
  presentation, which holds automatically because `G` and `Q` are of finite
  type over a field. Multiplicative type is Definition 12.17, with
  Theorem 12.8 (p.233) for the finitely generated character group.
- **Characterization.** Note 16.17 says that each of (a), (b), (c)
  characterizes `G_s`. Since Theorem 16.13 provides `G_s` with all three
  properties, this amounts to: a subgroup with property (b) has properties
  (a) and (c). Parts 1 and 2 state exactly these, with "largest" and
  "smallest" expressed by inclusions of ranges against every competitor.
  The existence of `G_s` itself is Theorem 16.13(a) and is not stated here.
- **Base change.** "The formation of `G_s` commutes with extension of the
  base field" says `(G_K)_s = (G_s)_K`. By property (a), `(G_K)_s` is the
  largest subgroup of `G_K` of multiplicative type, so part 3 states that
  `S_K` is of multiplicative type and contains every closed subgroup of `G_K`
  of multiplicative type. The field `K` ranges over all field extensions of
  `k` in the universe `u`.
- **Smoothness and connectedness.** Smoothness of an algebraic group over
  `k` is smoothness of its structure morphism, and connectedness is
  connectedness of the underlying topological space. Parts 4 and 5 state the
  remark after the proof of Theorem 16.13 for `G_s`.
- **Not included.** The same remark for `G_u` (perfect `k`), Note 16.18 and
  Note 16.19 are not part of this statement.
- **Universes.** One universe `u` is used for the fields, the groups in
  `IsMultiplicativeType` and the schemes. This is a formalization
  convention.
