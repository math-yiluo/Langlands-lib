# Semisimplicity through the solvable radical

`Langlands.GroupScheme.SemisimpleRadicalCharacterizationStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, writing
`Gbar := (GroupScheme.baseChange (toAlgebraicClosure k)).obj G`,

```text
(IsSemisimple G ↔ HasTrivialSolvableRadical Gbar) ∧
  (IsConnectedReductive G → (IsSemisimple G ↔ HasTrivialSolvableRadical G)).
```

In words: let `G` be a smooth connected affine group scheme over a field `k`, and
`k̄` the algebraic closure of `k`.

1. `G` is semisimple in the Library's sense if and only if every smooth connected
   solvable normal closed subgroup of `G_{k̄}` is trivial, that is, the geometric
   radical `R(G_{k̄})` is trivial.
2. If `G` is connected reductive, then `G` is semisimple if and only if every
   smooth connected solvable normal closed subgroup of `G` over `k` itself is
   trivial, that is, the radical `R(G)` is trivial.

Every ingredient is an existing declaration, used without change:

- `IsSemisimple G` (from `Langlands.GroupScheme.Reductive.Semisimple`) is a
  structure with the two fields `IsConnectedReductive G` and `HasFiniteCenter G`.
  `HasFiniteCenter G` says that some closed subgroup `z : Z ⟶ G` has as image
  the full scheme-theoretic centre functor `center G`, and that `Z.X.hom` is
  finite. Nilpotents are retained. `Reductive/Semisimple.md` says that this
  definition takes Milne's finite-centre characterization (Proposition 19.10(c))
  as the definition, and that the module does not prove its equivalence with a
  radical-based definition. Part 1 of this statement is that equivalence.
- `IsConnectedReductive G` (from `Langlands.GroupScheme.Reductive.Basic`) is a
  structure with the four fields `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left` and `HasTrivialUnipotentRadical Gbar`: every smooth
  connected unipotent normal closed subgroup of `G_{k̄}` is trivial.
- `HasTrivialSolvableRadical H` (from
  `Langlands.GroupScheme.Rational.SolvableRadicalQuotient`), for a group scheme `H`
  over a field `F`, says: for every group scheme `H'` over `Spec F` and every
  closed subgroup `j : H' ⟶ H` (`IsClosedSubgroup j`) with `H'` smooth,
  connected and solvable (`IsSolvableGroupScheme H'`) and with normal image
  `SubgroupFunctor.range j`, that image is `⊥`. It does not choose a radical and
  does not assert that one exists. The Library theorem `solvableRadicalExistence`
  (`Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof`) gives a
  represented solvable radical `r` (`IsSolvableRadical r`, from
  `Langlands.GroupScheme.Rational.LeviSubgroup`) for every smooth connected
  affine group over a field. Its image contains the images of all the subgroups
  above. So `HasTrivialSolvableRadical H` holds exactly when that radical is
  trivial, which is Milne's `R(H) = e`.
- `IsSolvableGroupScheme H'` (from `Langlands.GroupScheme.Absolute.Borel`) says
  that the abstract group of points of the base change of `H'` to the algebraic
  closure of its base field, over that algebraic closure, is solvable. For `H'`
  over `k̄` this uses `AlgebraicClosure (AlgebraicClosure k)`. For smooth affine
  groups this agrees with Milne's Definition 6.26 of solvability, by Milne 6.31,
  6.30, 6.20(b) and 6.21, as explained in `Absolute/Borel.md`. That equivalence is
  not formalized. All subgroups tested here are smooth.
- `toAlgebraicClosure k` (from `Langlands.GroupScheme.Reductive.Basic`) is
  `Spec (AlgebraicClosure k) ⟶ Spec k`. `GroupScheme.baseChange f` (from
  `Langlands.AbelianScheme.GroupScheme`) is the actual scheme pullback along `f`
  with its induced group law.

Both parts assume `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
`ConnectedSpace G.X.left`. Part 2 also assumes `IsConnectedReductive G`, as
Proposition 19.10 does; Part 2 says nothing about groups that are not reductive.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

- 6.44, printed p. 135 (PDF p. 151), in Section 6h, whose introduction says
  "Throughout this section, all algebraic groups are affine.":

  > Let G be a connected group variety over k. Extensions and quotients of
  > solvable algebraic groups are solvable (6.27), and so G contains a largest
  > connected solvable normal subgroup variety (6.42). This is called the radical
  > R(G) of G. A connected group variety G over an algebraically closed field is
  > said to be semisimple if R(G) = e. A connected group variety over a field k is
  > semisimple if G_{k^a} is semisimple, i.e., if its geometric radical R(G_{k^a})
  > is trivial.

- Chapter 19, printed p. 397 (PDF p. 413): "Recall (6.44) that an algebraic group
  over a field k is said to be semisimple if it is smooth and connected and
  G_{k^a} has trivial radical."
- Proposition 19.10, printed p. 400 (PDF p. 416): "The following conditions on a
  reductive algebraic group G are equivalent: (a) G is semisimple; (b) R(G) = e;
  (c) Z(G) is finite."
- Conventions: 1.26, printed p. 13 (PDF p. 29): "group variety" = "smooth
  algebraic group". Printed p. 162 (PDF p. 178), before Chapter 9: "By 'algebraic
  group' we shall mean 'affine algebraic group' and by 'group variety' we shall
  mean 'affine group variety'." The `IsAffineHom G.X.hom` hypothesis records
  this convention, which applies to Chapter 19.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists
Chapter 6 corrections only on p. 136 (Example 6.48) and Chapter 19 corrections
only on p. 399 (Definitions 19.7 and 19.8). None concerns 6.44 or 19.10.

Correspondence with the source:

- Part 1 compares Milne's definition 6.44 (`G` smooth and connected with
  `R(G_{k^a}) = e`) with the Library's `IsSemisimple`. The right side
  `HasTrivialSolvableRadical Gbar` is `R(G_{k^a}) = e`, as explained above, with
  the algebraic closure `k^a = AlgebraicClosure k`. Milne does not state Part 1
  as one result; it combines 6.44 with 19.10. Milne's 19.10 assumes `G`
  reductive. For the direction from right to left, reductivity follows from
  `R(G_{k^a}) = e`: the unipotent radical `R_u(G_{k^a})` is a smooth connected
  normal unipotent subgroup, and unipotent groups are solvable (Proposition
  14.21, printed p. 284: "every unipotent algebraic group is nilpotent (a
  fortiori solvable)"), so `R_u(G_{k^a}) ⊆ R(G_{k^a}) = e`.
- Part 2 is 19.10, (b) if and only if (c), for reductive `G`, with (c) replaced
  by the Library's `IsSemisimple G`. Given `IsConnectedReductive G`,
  `IsSemisimple G` is equivalent to `HasFiniteCenter G`, which is Milne's (c):
  Milne's centre `Z(G)` is the scheme-theoretic centre, which need not be smooth
  (printed p. 400, before 19.10: "the centre of a reductive group need be neither
  smooth nor connected").

The provenance is derived for three reasons:

1. Part 1 is assembled from 6.44, 19.10 and 14.21, as just explained.
2. The radical conditions are stated through `HasTrivialSolvableRadical`, which
   tests all smooth connected solvable normal closed subgroups, and solvability is
   the Library's `IsSolvableGroupScheme`. Neither is literally Milne's
   formulation.
3. `k` lies in an arbitrary universe `u`, and `k^a` is Mathlib's
   `AlgebraicClosure k`. These are formalization conventions.

## For the later proof (not part of this unit)

Milne's proof of 19.10, printed p. 400: "(a)⇔(b). As the formation of R(G)
commutes with extension of the base field, R(G) = e if and only if R(G_{k^a}) =
e. (b)⇔(c). As R(G) is the largest subtorus of the multiplicative group Z(G),
the quotient Z(G)/R(G) is finite, and so Z(G) is finite if R(G) = e.
Conversely, if Z(G) is finite, then R(G) = e because it is a torus." This uses
Corollary 17.62, printed p. 372 (PDF p. 388): for reductive `G`, (a) `Z(G)` is
of multiplicative type, (b) `R(G) = Z(G)_t`, the largest subtorus of `Z(G)`, and
(c) the formation of `R(G)` commutes with extension of the base field.

Possibly useful published Library results: `solvableRadicalExistence`,
`reductiveGeometricSolvableRadicalExists`
(`Rational/ReductiveGeometricSolvableRadicalExistsProof`; for connected
reductive `G`, a represented solvable radical that remains one over `k̄`),
`HasTrivialSolvableRadical.hasFiniteCenter`
(`Reductive/CentralTorusSemisimpleQuotientReduction`; over an algebraically
closed field, for affine `G` locally of finite type),
`HasFiniteCenter.baseChange` (`Reductive/FiniteCenterBaseChange`),
`HasFiniteCenter.of_fieldExtension` (`Reductive/FiniteCenterReflection`), and
`isSolvable_points_of_isUnipotent` (`Absolute/UnipotentPointsSolvable`).
