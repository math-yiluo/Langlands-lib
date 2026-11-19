# Torus-stable subgroups of connected unipotent groups

`Langlands.GroupScheme.TorusStableUnipotentSubgroupConnectedStatement.{u}`
is a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and let `U` and `T` be group schemes over
`Spec (CommRingCat.of k)` with `[LocallyOfFiniteType U.X.hom]`,
`[IsAffineHom U.X.hom]`, `ConnectedSpace U.X.left`, `IsUnipotent U` and
`IsTorus T`. For every action `a : AutomorphicAction T U`, both of the
following hold.

1. **Stable subgroups containing `U^T`.** For every group scheme `H` over
   `Spec k` and every homomorphism `h : H ⟶ U` with `IsClosedSubgroup h`,
   `a.IsStable (SubgroupFunctor.range h)` and
   `a.fixedSubgroup ≤ SubgroupFunctor.range h`, the space `H.X.left` is
   connected (`ConnectedSpace H.X.left`).
2. **The fixed subgroup.** For every group scheme `F` over `Spec k` and every
   homomorphism `j : F ⟶ U` with `IsClosedSubgroup j` and
   `SubgroupFunctor.range j = a.fixedSubgroup`, `ConnectedSpace F.X.left`.

The ingredients are existing declarations, used without change.

- `AutomorphicAction T U` (from [`AutomorphicAction`](../AutomorphicAction.md))
  is an action of `T` on `U` by group automorphisms: a morphism
  `T.X ⊗ U.X ⟶ U.X` over the base whose induced maps on points over every
  test scheme form an action of the group of points of `T`, each acting
  point inducing a group homomorphism of the points of `U`.
- `a.fixedSubgroup` (same module) is the subgroup functor of points `g` of
  `U` over a test scheme `S'` such that, for every morphism `b : S'' ⟶ S'`
  of test schemes and every point `t` of `T` over `S''`, `t` acting on the
  pullback of `g` to `S''` gives that pullback back.
- `a.IsStable F` (from [`RepresentedAction`](../RepresentedAction.md)) says
  that, on every test scheme, acting points of `T` map points of `F` to
  points of `F`.
- `IsClosedSubgroup h` (from [`Reductive.Basic`](../Reductive/Basic.md))
  says that the underlying morphism of schemes of `h` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `IsTorus T` (from [`Torus.Lattice`](../Torus/Lattice.md)) says that there
  is a field extension `K : Type u` of `k` such that the base change `T_K` is
  a split torus, that is (from [`Torus.Split`](../Torus/Split.md))
  isomorphic as a group scheme to a finite product of copies of `G_m`.
- `SubgroupFunctor.range h` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of points of `U` that factor through `h`; `≤` is
  inclusion on every test scheme. `ConnectedSpace X.left` says that the
  underlying topological space is connected (in particular nonempty).

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.25, p.331: "Let U be a connected unipotent algebraic group
  acted on by a torus T. Every algebraic subgroup H of U stable under T and
  containing U^T is connected. In particular, U^T is connected."
- Section 2f, p.50: "Let N and Q be algebraic groups, and suppose that there
  is given an action of Q on N, (q, n) ↦ θ_R(q, n): Q(R) × N(R) → N(R), such
  that, for every q, the map n ↦ θ_R(q, n) is a group homomorphism."
- Theorem 7.1, p.138: "The functor R ⇝ {x ∈ X(R) | μ(g, x_{R′}) = x_{R′}
  for all g ∈ G(R′) and all R-algebras R′} is represented by a closed
  subscheme X^G of X." The following text: "The subscheme X^G is called the
  fixed subscheme for the action."
- Definition 12.14, p.236: "An algebraic group over k is a torus if it
  becomes isomorphic to a finite product of copies of G_m over some field
  containing k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- Proposition 1.41, p.18: "Algebraic subgroups of algebraic groups are
  closed (in the Zariski topology)."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine
  over a base field k."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.25 on
printed p.331 with the same words. Its Theorem 7.1 (p.138) has the same
content, with the quantifiers written "for all R-algebras R′ and
g ∈ G(R′)".

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.50, 135, 138,
236 or 331. Their p.18 entry concerns the proof of Proposition 1.40, not
Proposition 1.41. Their p.324 entry replaces "diagonalizable" with
"trigonalizable" in the last sentence of the first paragraph of Chapter 16;
it does not concern the affineness sentence. The 2022 errata have no entry
for pp.50, 135, 138, 236, 324 or 331; their p.18 entry concerns the proof of
Proposition 1.37.

## Derivation from the source

- **The groups.** Milne's algebraic groups are group schemes of finite type
  over `k`, affine by the Chapter 16 convention. For `U` the statement
  assumes `LocallyOfFiniteType U.X.hom` and `IsAffineHom U.X.hom` (an affine
  morphism is quasi-compact, so `U` is of finite type), `ConnectedSpace` and
  `IsUnipotent`. For `T` it assumes `IsTorus T` (Definition 12.14); such a
  `T` becomes isomorphic to a split torus over a field extension, so it is
  affine and of finite type by descent along the faithfully flat
  quasi-compact morphism `Spec K ⟶ Spec k`, and no further hypothesis on `T`
  is imposed.
- **The action.** "`U` acted on by a torus `T`" is an action of the algebraic
  group `T` on the algebraic group `U` by group homomorphisms, as on p.50.
  `AutomorphicAction T U` is such an action, given by one morphism of
  schemes and tested on all schemes over `Spec k`; on affine test schemes
  this is Milne's natural action on `R`-points.
- **`U^T`.** By Theorem 7.1 the fixed subscheme `U^T` represents the functor
  of points fixed by all points of `T` over all `R`-algebras `R′`. This is
  `a.fixedSubgroup`, tested on all schemes and all refinements. Part 2
  formalizes "`U^T` is connected" for every closed subgroup representing
  `a.fixedSubgroup`.
- **The subgroup `H`.** An algebraic subgroup is a group scheme with a
  homomorphism to `U` that is a closed immersion (Proposition 1.41).
  "Stable under `T`" is `a.IsStable (SubgroupFunctor.range h)`, and
  "containing `U^T`" is `a.fixedSubgroup ≤ SubgroupFunctor.range h`, both
  tested on every scheme over `Spec k`. Connectedness is connectedness of
  the underlying topological space.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
