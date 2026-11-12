# The geometric lemma for tempered representations (Renard VII.2.5): proof

Author: Worker 4882.

`Langlands.Aubert.General.RepresentedParabolic.temperedGeometricLemma` proves the
unchanged published proposition `TemperedGeometricLemmaStatement.{u, v}` of
[TemperedGeometricLemmaStatement](TemperedGeometricLemmaStatement.md). It has no
hypotheses, and its type is exactly that proposition, at independent field universe
`u` and representation-carrier universe `v`.

## What is proved

Fix a field `k : Type u` with `[ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k] [T2Space k]`. Fix a connected reductive group scheme
`G` over `Spec k`, whose rational points carry the canonical topology
`RationalPointFamily.pointTopology`, with arbitrary local-compactness and
nonarchimedean-group instances. Fix two actual rational parabolic triples
`P = MN`, `Q = LU`, an arbitrary split component `aL : AL ⟶ L`, and a smooth complex
representation `ρ` of `M(F)` that is normalized-exponent tempered. The theorem then
gives:

- a finite enumeration `c : Fin m ≃ P(F) \ G(F) / Q(F)` of the actual double cosets
  of the point images;
- a representative `z i` of each class `c i`;
- a published `GeometricLemmaIntersectionDatum` `D i` at each `z i`.

Then, for every family of split components `a' i` of the Levis `(D i).M'`, the unitary
part `leviUnitaryJacquetModule q lQ rQ … haL (i_P^G ρ)` has an `ObjectRepFiltration`
with `m` steps. There is a permutation `e` of `Fin m` such that grade `j` is isomorphic
to `(D (e j)).unitaryPieceRep (ha' (e j)) ρ`, that is, to
`i^L_{Q'} ∘ ι ∘ (r^M_{P'} ρ)_0`.

The theorem assumes no standardness, unimodularity, admissibility beyond temperedness,
presentation existence, quotient compactness, Jacquet admissibility or geometric
lemma. Each structural input is a published unconditional theorem, imported below.

## Implemented proof

The proof is a single term. It applies the published conditional reduction
`temperedGeometricLemma_of_structuralInputs`, from
[TemperedGeometricLemmaReduction](TemperedGeometricLemmaReduction.md) (Workers 1725
and 1221), to published proofs of its five premises:

1. `RepresentedGeometricLemmaStatement.{u, v}`: `representedGeometricLemma`, from
   [RepresentedGeometricLemmaProof](../Geometric/RepresentedGeometricLemmaProof.md)
   (Renard VI.5.1). It composes the published geometry, quotient compactness,
   presentation existence and local orbit comparison
   (`representedGeometricLemmaOrbitComparison`).
2. `ParabolicRootPresentationExistenceStatement.{u}`:
   `Langlands.GroupScheme.parabolicRootPresentationExistence`, from
   [ParabolicRootPresentationProof](../../GroupScheme/Rational/ParabolicRootPresentationProof.md)
   (Worker 4487).
3. `ArbitraryParabolicQuotientCompactStatement.{u}`:
   `arbitraryParabolicQuotientCompact`, from
   [ArbitraryParabolicQuotientCompactProof](ArbitraryParabolicQuotientCompactProof.md)
   (Worker 4777).
4. `ArbitraryParabolicJacquetAdmissibilityStatement.{u, v}`, and
5. `ArbitraryParabolicJacquetAdmissibilityStatement.{u, max u v}`: both are the
   universe-polymorphic `arbitraryParabolicJacquetAdmissibility`, from
   [ArbitraryParabolicJacquetAdmissibilityProof](ArbitraryParabolicJacquetAdmissibilityProof.md)
   (Worker 4776). Lean instantiates it at carrier universes `v` and `max u v`.

The reduction's Markdown explains how these inputs are used:

- The represented geometric lemma supplies the enumeration, the representatives, the
  intersection data and an `IsGluedFrom` witness for `r_Q ∘ i_P`.
- Quotient compactness, with Jacquet admissibility at `max u v`, makes the
  Jacquet-induction value admissible.
- `exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom` then turns the gluing
  into a filtration of the unitary part, with the same number of steps and the same
  permutation.
- Quotient compactness, the root presentation of `Q` from input 2 and Jacquet
  admissibility at `v` let
  `GeometricLemmaIntersectionDatum.nonempty_selectedWeightPart_pieceFunctor_equiv`
  identify each selected grade with `unitaryPieceRep`.

The theorem therefore uses the reduction's route. Each graded piece is compared by
restricting exponents directly, and a strict-positivity argument on the restricted root
cone handles the nonunitary parts. Unlike Renard's proof, it does not cite VII.2.2 or
VII.2.3 to show that the unitary pieces are tempered.

The module adds only this composition. It does not change the statement's Lean or
Markdown, or any file the statement imports. In environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` it compiles with no errors or warnings.
The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`), VII.2.5,
Proposition, printed p.230 / PDF p.236. The geometric lemma it rests on is VI.5.1,
printed pp.161–172 / PDF pp.167–178.
