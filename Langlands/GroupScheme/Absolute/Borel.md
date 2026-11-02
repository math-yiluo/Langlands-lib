# Solvable, Borel and parabolic subgroups over a field

Worker 1234.

This module defines the absolute structure notions for group schemes over a
field: solvable group schemes, Borel subgroups, parabolic subgroups, Borel pairs
and regular cocharacters. It defines notions only. The structure theorems about
them are stated in `Langlands.GroupScheme.Absolute.BorelStatement`. No
definition contains a structure theorem (conjugacy, existence, completeness of
`G/B`, Bruhat) as a field or hypothesis. Parabolic subgroups are not defined as
dynamic `P(λ)`; that identification is a separate statement.

Throughout, `k : Type u` is a field, `S = Spec (CommRingCat.of k)`, and group
schemes are `Langlands.GroupScheme S`. Write `k̄ = AlgebraicClosure k` and
`G_{k̄}` for the base change
`(GroupScheme.baseChange (toAlgebraicClosure k)).obj G` along the published
`toAlgebraicClosure k : Spec k̄ ⟶ Spec k`. A closed subgroup is a homomorphism
`i` with the published `IsClosedSubgroup i`, which says the underlying morphism
of schemes is a closed immersion.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- Proposition 6.20(b), Proposition 6.21, Definition 6.26, Proposition 6.30 and
  Corollary 6.31, printed pp.130–132 (PDF 146–148): derived groups and their
  `k̄`-points, solvable algebraic groups, the derived series, and invariance of
  solvability under field extension.
- Definition 17.6 and Example 17.7, printed pp.353–354 (PDF 369–370): Borel
  subgroups, and those of `GL_V`.
- Definition 17.12, printed p.355 (PDF 371): Borel pairs.
- Definition 17.15 and Theorem 17.16, printed p.356 (PDF 372): parabolic
  subgroups, and the criterion of containing a Borel subgroup.
- Definition 21.26, printed p.433 (PDF 449): regular cocharacters.

## `IsSolvableGroupScheme G`

`IsSolvableGroupScheme G` says that the abstract group
`Over.mk (𝟙 (Spec k̄)) ⟶ G_{k̄}.X` is solvable (Mathlib's `Group.IsSolvable`).
This group is `G_{k̄}(k̄)`, the `k̄`-points of `G_{k̄}` over `Spec k̄`, with the
group law of points of a group object.

This definition is a **derived reformulation**. Milne, Definition 6.26, calls an
algebraic group solvable when it has a subnormal series of algebraic subgroups
with commutative quotients. For a smooth affine `G` the two notions agree:

- by Corollary 6.31, `G` is solvable if and only if `G_{k̄}` is;
- by Proposition 6.30, `G_{k̄}` is solvable if and only if its derived series
  of algebraic subgroups ends with `e`;
- by Proposition 6.20(b) and Proposition 6.21, over the algebraically closed
  field `k̄` the derived group of a group variety has as `k̄`-points the derived
  group of the `k̄`-points. A group variety is determined by its `k̄`-points,
  so the algebraic derived series ends with `e` if and only if the abstract
  derived series of `G_{k̄}(k̄)` does.

This equivalence is not formalized. The notion is only used for smooth group
schemes (Borel subgroups below are smooth by definition); for non-smooth group
schemes it says nothing about the infinitesimal structure.

## `IsBorelSubgroup i`

For group schemes `B G` over `S` and a homomorphism `i : B ⟶ G`,
`IsBorelSubgroup i` is a structure with five fields:

- `isClosedSubgroup : IsClosedSubgroup i`;
- `smooth : Smooth B.X.hom`, so `B` is smooth over `S`;
- `connectedSpace : ConnectedSpace B.X.left`, so the underlying space of `B` is
  connected;
- `isSolvableGroupScheme : IsSolvableGroupScheme B`;
- `maximal`: for every group scheme `B'`, every `i' : B' ⟶ G` with
  `IsClosedSubgroup i'`, `Smooth B'.X.hom`, `ConnectedSpace B'.X.left` and
  `IsSolvableGroupScheme B'`, and every homomorphism `f : B ⟶ B'` with
  `f ≫ i' = i`, the homomorphism `f` is an isomorphism (`IsIso f`).

This is Milne, Definition 17.6: a Borel subgroup is a maximal connected solvable
subgroup variety. A subgroup variety is a smooth algebraic subgroup, here a
smooth closed subgroup. Maximality is expressed through homomorphisms, with the
same pattern as the published `IsMaximalTorus`. Milne states the definition for
a connected group variety `G` over an algebraically closed field. Here `G` is
any group scheme over any field `k`, and maximality is among closed subgroups
defined over `k`. This extension is **derived**. For `k` algebraically closed
and `G` a connected group variety it is Milne's definition.

## `IsParabolicSubgroup i`

For `i : P ⟶ G`, `IsParabolicSubgroup i` is a structure with three fields:

- `isClosedSubgroup : IsClosedSubgroup i`;
- `smooth : Smooth P.X.hom`;
- `exists_isBorelSubgroup`: there are a group scheme `B` over `Spec k̄`, a
  homomorphism `j : B ⟶ G_{k̄}` and a homomorphism `f : B ⟶ P_{k̄}` with
  `IsBorelSubgroup j` and `f ≫ i_{k̄} = j`, where
  `i_{k̄} = (GroupScheme.baseChange (toAlgebraicClosure k)).map i`. So some
  Borel subgroup of `G_{k̄}` factors through the base change of `i`.

This definition is **derived from Milne, Theorem 17.16**. Milne, Definition
17.15, calls a subgroup variety `P` of a connected group variety `G` over any
field parabolic when `G/P` is complete. Quotients `G/P` are not available in
the Library. Theorem 17.16 shows that `P` is parabolic if and only if it
contains a Borel subgroup. Borel subgroups are defined over an algebraically
closed field, and `G/P` is complete if and only if its base change
`G_{k̄}/P_{k̄}` is, so the criterion is applied to `P_{k̄}` in `G_{k̄}`.

The field `smooth` records that Milne's parabolic subgroups are subgroup
varieties, that is, smooth, as the task requires. Without it, in characteristic
`p` the closed subgroup of `GL_2` cut out by `c^p = 0`, with `c` the lower-left
entry, would count as parabolic. It contains the upper triangular Borel
subgroup, but its coordinate ring contains the nonzero nilpotent `c`, so it is
not reduced and not of the form `P(λ)` (for smooth `G` these are smooth).

## `IsBorelPair i j`

For `i : B ⟶ G` and `j : T.toGrp ⟶ G` with `T` a commutative group scheme over
`S`, `IsBorelPair i j` is the conjunction of:

- `IsBorelSubgroup i`;
- `IsMaximalTorus j`, the published notion of a maximal torus;
- there is `f : T.toGrp ⟶ B` with `f ≫ i = j`, so `j` factors through `i`.

This is Milne, Definition 17.12: a pair `(B, T)` with `T` a maximal torus and
`B` a Borel subgroup containing `T`. Milne works over an algebraically closed
field. Use over a general field is **derived**, as for `IsBorelSubgroup`.

## `IsRegularCocharacter j ν`

For a commutative group scheme `T` over `S`, a group scheme `G` with
`[IsAffineHom G.X.hom]`, a homomorphism `j : T.toGrp ⟶ G` and a cocharacter
`ν : cocharacterLattice T` (a homomorphism `Gm S ⟶ T`),
`IsRegularCocharacter j ν` says: for every `α` in the published `roots j`,
`latticePairing T α ν ≠ 0`. Here `roots j` are the nonzero characters of `T`
with a nonzero weight space in the Lie algebra of `G`, and `latticePairing T α ν`
is the integer `⟨α, ν⟩` determined by the endomorphism `ν ≫ α` of `𝔾_m`.

This is Milne, Definition 21.26, for a split reductive group `(G, T)`: a
cocharacter `λ` of `T` is regular if `⟨α, λ⟩ ≠ 0` for all roots `α`. The
definition does not require `j` to be a maximal torus, and the uses of this
notion in `Langlands.GroupScheme.Absolute.BorelStatement` assume that
separately. The formula for an arbitrary homomorphism `j` is **derived**.
