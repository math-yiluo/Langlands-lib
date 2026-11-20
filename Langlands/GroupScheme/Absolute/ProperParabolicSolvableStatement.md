# Proper parabolic subgroups and solvability

`Langlands.GroupScheme.ProperParabolicSolvableStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be an algebraically closed field, put
`S = Spec (CommRingCat.of k)`, and let `G : GroupScheme S` satisfy
`[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`.
Then the following are equivalent:

1. there are `P : GroupScheme S` and `i : P ⟶ G` with
   `IsParabolicSubgroup i` and `¬ IsIso i`;
2. `¬ IsSolvableGroupScheme G`.

The ingredients are existing declarations, used without change.

- `IsParabolicSubgroup i` (from [`Absolute.Borel`](Borel.md)) says that `i`
  is a closed subgroup (its underlying morphism of schemes is a closed
  immersion), that `P` is smooth, and that some Borel subgroup of the base
  change `G_{k̄}` of `G` to `k̄ = AlgebraicClosure k` factors through the base
  change of `i`.
- `IsIso i` (Mathlib) says that `i` is an isomorphism of group schemes. As
  `i` is a closed immersion, `¬ IsIso i` says that `P` is a proper subgroup
  of `G`.
- `IsSolvableGroupScheme G` (from [`Absolute.Borel`](Borel.md)) says that the
  abstract group of `k̄`-points of `G_{k̄}` is solvable.
- `IsAlgClosed k` and `Smooth` are from Mathlib; `ConnectedSpace G.X.left`
  says that the underlying topological space of `G` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 17.17, p.356: "A connected group variety contains a proper
  parabolic subgroup if and only if it is not solvable."
- Definition 17.15, p.356: "Let G be a connected group variety over a field
  k (not necessarily algebraically closed). A subgroup variety P of G is
  parabolic if G/P is complete."
- Theorem 17.16, p.356: "A subgroup variety P of G is parabolic if and only
  if it contains a Borel subgroup."
- Section 17b, p.353: "In this section, G is a connected group variety over
  an algebraically closed field k." Corollary 17.17 is in Section 17b.
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are
  affine over a base field k".
- p.13: "“group variety” = “smooth algebraic group”."

Milne's proof, for orientation only: "Let H be a connected group variety.
If H is solvable, the only Borel subgroup of H is H itself, and so H
contains no proper parabolic subgroup. If is not solvable, then the Borel
subgroups of H are proper parabolic subgroups." (The 2017 text omits the
subject "H" in the last sentence; the 2022 reprint reads "If H is not
solvable".)

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) has Definition 17.15 and
Theorem 17.16 on printed p.356 and Corollary 17.17 on p.357. Corollary 17.17
and Theorem 17.16 have the same words. Definition 17.15 is worded
differently: "A parabolic subgroup of G is a subgroup variety such that G/P
is complete. The same definition applies even when k is not algebraically
closed." It has the same meaning. The Section 17b convention is on p.354
with the same words, the Chapter 17 opening on p.352 contains the quoted
affineness sentence with the same words, and the quoted sentence on group
varieties is on p.14.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata have no entry for pp.13, 352, 353 or
356. The 2022 errata have no entry for reprint pp.14, 352, 354, 356 or 357.

## Derivation from the source

- **The group.** A connected group variety over `k` is a smooth algebraic
  group (p.13), affine by the Chapter 17 convention, with connected
  underlying space: `Smooth G.X.hom` (so `G` is locally of finite type),
  `IsAffineHom G.X.hom` (so quasi-compact, hence of finite type) and
  `ConnectedSpace G.X.left`. The field is algebraically closed throughout
  Section 17b.
- **Parabolic subgroups.** The Library's `IsParabolicSubgroup` uses the
  criterion of Theorem 17.16 in place of Definition 17.15, as explained in
  [`Absolute.Borel`](Borel.md): a smooth closed subgroup containing a Borel
  subgroup after base change to `k̄`. By Theorem 17.16 the two agree for
  subgroup varieties. The quotients of Definition 17.15 are also available
  in the Library. `smoothSubgroupQuotientExistence` (in
  `Langlands.GroupScheme.HomogeneousQuotientProof`) constructs, for a
  smooth closed subgroup of a smooth affine group over a field, a smooth
  surjective morphism `q : G.X ⟶ Q` whose fibres are exactly the cosets on
  every test scheme. `parabolicSubgroupQuotientProper` (in
  `Langlands.GroupScheme.ParabolicQuotientProperProof`) proves that such a
  quotient is proper when `G` is connected and `IsParabolicSubgroup i`
  holds, which is one direction of Theorem 17.16. Here `k` is algebraically
  closed, so `k → k̄` is an isomorphism and `IsParabolicSubgroup i` says
  that `P` contains a Borel subgroup of `G`.
- **Proper.** "Proper parabolic subgroup" means a parabolic subgroup
  different from `G`. For a closed subgroup `i`, being different from `G`
  is `¬ IsIso i`.
- **Solvability.** For smooth affine groups, `IsSolvableGroupScheme G`
  agrees with Milne's solvability (Definition 6.26), as explained in
  [`Absolute.Borel`](Borel.md).
- **The field.** Milne states the corollary under the Section 17b
  convention, so the hypothesis `IsAlgClosed k` is kept. The statement makes
  no claim over other fields.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
