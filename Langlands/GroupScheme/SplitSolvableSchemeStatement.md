# The underlying scheme of a split solvable group

`Langlands.GroupScheme.SplitSolvableSchemeProductStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field, put `S = Spec (CommRingCat.of k)`, and let
`G : GroupScheme S` satisfy `IsSplitSolvableGroupScheme G`. Let `U` and `D`
be group schemes over `S` with homomorphisms `i : U ⟶ G` and `q : G ⟶ D`,
and assume `IsClosedSubgroup i`, `IsUnipotent U`,
`(SubgroupFunctor.range i).IsNormal`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` and
`IsMultiplicativeType D`. Write `𝔸^r` for
`Over.mk (𝔸(ULift.{u} (Fin r); S) ↘ S)` and `T_m` for
`splitTorus S (ULift.{u} (Fin m))`. Then there are natural numbers `r` and `m`
such that

- `U.X ≅ 𝔸^r` (an isomorphism of schemes over `S`);
- `D ≅ T_m` (an isomorphism of group schemes over `S`);
- `G.X ≅ 𝔸^r ⊗ T_m.X` (an isomorphism of schemes over `S`; `⊗` is the fibre
  product over `S`).

The ingredients are existing declarations, used without change.

- `IsSplitSolvableGroupScheme G` (from [`SplitSolvable`](SplitSolvable.md))
  says that `G` is smooth, affine, connected and solvable, and has a finite
  series of closed, smooth, connected subgroups, each normal in the previous
  one with represented fppf quotient isomorphic over `k` to `G_a` or `G_m`,
  ending with the trivial group.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
  `IsUnipotent U` (same module) says that every nonzero finite-dimensional
  matrix representation of `U` has a nonzero fixed vector (Milne 6.45).
- `SubgroupFunctor.range i` (from [`SubgroupFunctor`](SubgroupFunctor.md))
  is the subgroup functor of points of `G` that factor through `i`.
  `RelativeRoot.IsFppfQuotient N q` (from
  [`Rational.RootSubgroupStructureStatement`](Rational/RootSubgroupStructureStatement.md))
  says that the underlying morphism of `q` is flat, surjective and locally
  of finite presentation, with actual kernel equal to `N` on every test
  scheme.
- `IsMultiplicativeType D` (from
  [`Torus.MultiplicativeType`](Torus/MultiplicativeType.md)) says that `D`
  becomes diagonalizable over some field extension of `k`.
- `splitTorus S I` (from [`Torus.Split`](Torus/Split.md)) is the split torus
  `G_m^I` over `S`, the categorical product of copies of `G_m` indexed by the
  finite type `I`.
  `𝔸(ι; S)` (Mathlib) is affine space over `S` with coordinates indexed by
  `ι`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 16.56, p.344: "Let G be a split solvable algebraic group over k.
  The underlying scheme of G is isomorphic to A^r × (A^1 ∖ 0)^{n−r}, where
  n = dim G and r = dim G_u. Hence Pic(G) = 0."
- Its proof: "The scheme G is a G_u-torsor over G/G_u (see 2.68). This torsor
  is trivial by (b) of the proposition, and so G ≃ G_u × G/G_u as algebraic
  schemes. Here G/G_u is a split torus, and so it is isomorphic to
  G_m^{n−r}. On the other hand, G_u has a subnormal series with quotients
  isomorphic to G_a. An induction argument using (b) of the proposition
  shows that G_u ≃ A^r (as a scheme)."
- Definition 6.33, p.132: "A solvable algebraic group G over k is split if it
  admits a subnormal series G = G_0 ⊃ G_1 ⊃ ⋯ ⊃ G_n = e such that each
  quotient G_i/G_{i+1} is isomorphic to G_a or to G_m."
- Theorem 16.6, pp.325–326: "When these conditions hold, G_u is unique and
  contains every unipotent algebraic subgroup of G." Notation 16.7, p.326:
  "When G is an algebraic group, we use G_u exclusively to denote a normal
  algebraic subgroup such that G_u is unipotent and G/G_u is of
  multiplicative type."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 16.56 on
printed p.344 with the same words, and moves the sentence "For example, the
underlying scheme of a smooth connected unipotent group U over a perfect
field is isomorphic to A^{dim(U)}" from after the proof to before it.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for pp.132, 325, 326 or 344.

## Derivation from the source

- **Split solvable group and `G_u`.** Milne's split solvable group
  (Definition 6.33) is smooth, connected, affine and solvable with a
  subnormal series with quotients `G_a` or `G_m`; this is
  `IsSplitSolvableGroupScheme G`. `G_u` and `D = G/G_u` are as in
  Notation 16.7; the hypotheses on `i` and `q` say that `U` is a normal
  unipotent closed subgroup and `q` a quotient map with kernel `U` onto a
  group of multiplicative type, so `U = G_u` by the uniqueness in
  Theorem 16.6. Existence of such `i` and `q` is not part of the statement.
- **The dimensions.** `A^r × (A^1 ∖ 0)^{n−r}` is `𝔸^r ⊗ T_{n−r}.X`, since the
  underlying scheme of the split torus `G_m^{n−r}` is `(A^1 ∖ 0)^{n−r}`.
  Instead of the numbers `dim G` and `dim G_u`, the statement records the
  isomorphisms `U.X ≅ 𝔸^r` and `D ≅ T_m`, which force `r = dim G_u` and
  `m = dim D = dim G − dim G_u`, so `m = n − r`. These two isomorphisms are
  established in Milne's proof ("G_u ≃ A^r (as a scheme)" and "G/G_u is a
  split torus ... isomorphic to G_m^{n−r}"); the statement asserts them
  together with the isomorphism for `G`.
- **Not included.** The consequence `Pic(G) = 0` is not part of this
  statement.
- **Related Library statement.** `SplitUnipotentAffineSpaceStatement` (in
  [`Unipotent.SplitAffineSpaceStatement`](Unipotent/SplitAffineSpaceStatement.md),
  Milne 14.66) states that a split unipotent group with a series of length
  `n` is isomorphic to `𝔸^n` as a scheme.
- **Universes.** One universe `u` is used for the field and the schemes; the
  index types `ULift.{u} (Fin r)` and `ULift.{u} (Fin m)` live in it. This is
  a formalization convention.
