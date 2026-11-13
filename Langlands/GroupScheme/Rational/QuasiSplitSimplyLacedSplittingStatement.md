# Splitting from a reduced simply-laced relative root system

Worker 227. This module defines a general proposition and the predicate in its
hypothesis. It does not prove the proposition.

## The full relative root set

Let `k : Type u` be an arbitrary field, `G` a group scheme over `Spec k`
with affine structure morphism, `S` a commutative group scheme over `Spec k`,
and `i : S.toGrp ⟶ G`. The predicate
`HasReducedSimplyLacedRelativeRootSystem i` asserts that there exist a finite
type `J : Type u` and a root pairing

`P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))`

with all the following properties:

- The roots and coroots span their ambient rational vector spaces
  (`P.IsRootSystem`).
- The root-coroot pairings are integral (`P.IsCrystallographic`).
- Any linearly dependent roots differ by a sign (`P.IsReduced`).
- `P.toLinearMap` is the ordinary evaluation pairing with the dual.
- The image of every root of `P`, in the rationalized character lattice of
  `S`, is exactly `toRat '' relativeRoots i`.
- For every two root indices `a, b`, `P.pairing a b = P.pairing b a`.

The final condition expresses simple lacing on each irreducible component.
The root-image equality concerns the entire published set of relative roots:
the nonzero characters of `S` with a nonzero adjoint weight space. In
particular, one cannot satisfy the predicate for a nonreduced root set by
keeping only its indivisible roots or only its nonmultipliable roots.
The definition uses the rational-span and evaluation conventions of
`HasRelativeRootSystem` in `Rational/Statement`, but does not ask for a
comparison with the rational Weyl group.

## The statement

`Langlands.GroupScheme.QuasiSplitSimplyLacedSplittingStatement.{u}` says:
over every field `k : Type u`, let `G` be quasi-split and absolutely
almost-simple. If `i : S.toGrp ⟶ G` is an actual maximal split torus and
`HasReducedSimplyLacedRelativeRootSystem i` holds, then `IsMaximalTorus i`.

Here `IsQuasiSplit G` includes connected reductivity and the existence of a
field-defined geometric Borel subgroup. `IsAbsolutelyAlmostSimple G`
includes almost-simplicity over the field and after base change to its
algebraic closure. `IsMaximalSplitTorus i` includes splitness of `S` and its
closed immersion into `G`. Thus the conclusion says that this same split
subtorus is maximal among all tori. The `haveI` in the statement supplies
affineness from connected reductivity; it adds no premise.

The statement applies in every characteristic, over imperfect as well as
perfect fields, and at every universe `u`. It has no valuation, local-field,
rank-one, or simply connected hypothesis.

## Derived provenance

The proposed criterion isolates the finite-root folding input of the
splitting step in Kaletha–Prasad's proof of Theorem 10.3.1. It is a derived
general prerequisite, rather than a literal transcription of a numbered
theorem in that book.

Milne, *Algebraic Groups*, corrected reprint (2022), §25.b,
25.16–25.19, printed pp.552–553 / PDF pp.563–564, identifies the full
relative roots in their rational span and as the nonzero restrictions of
absolute roots. In §25.c, Proposition 25.28(a), printed p.555 / PDF p.566,
the quasi-split condition makes every absolute simple root distinguished
and identifies the star action with the ordinary action. These are the
group-theoretic conventions behind the predicate and the anticipated
folding proof. Milne does not state the present implication there.

For comparison, Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 6.4.8, Remark 6.4.9 and Table 6.4.1, printed
pp.225–227 / PDF pp.256–258, list the relative and affine root types
for quasi-split absolutely almost-simple groups in their valued-field
setting. The nontrivial outer foldings in the finite relative-root column
have types `BC_n`, `C_n`, `B_(n-1)`, `G₂`, or `F₄`, with the usual
rank restrictions on the absolute types. These are nonreduced or have
unequal root lengths. The general statement above requires the
corresponding finite-root and descent argument over arbitrary fields;
the valued-field table alone is not a proof of that stronger scope.

The authors' corrections of 1 November 2024, p.32, correct
Remark 6.4.7's `²D_(2n), B_n` to `²D_n, B_(n-1)`. They contain no
correction to Proposition 6.4.8 or Table 6.4.1. Milne's retained official
errata snapshot of 4 November 2026 has no correction to the cited passages.

## Remaining proof and application

A proof must establish the finite-root folding criterion for actual
relative roots and use quasi-split descent to show that the given maximal
split torus is maximal as a torus. Neither obligation is assumed as an
unproved theorem in this module: they remain the content of the proposition.

The module constructs no chamber, affine roots, Cartan matrix or positive
marks. It does not show that the predicate holds for the maximal
unramified base change of an anisotropic local-field group, compare such
relative roots with an arbitrary actual absolute Tits index, or prove
`LocalAnisotropicAffineDiagramStatement`.
