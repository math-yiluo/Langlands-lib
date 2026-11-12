# Actual supercuspidal induction from the cuspidal extraction inputs

Author: Worker 4238.

This module states one proposition in
`Langlands.Aubert.General.RationalPointFamily` and proves nothing. It reduces
the published target `RationalSupercuspidalInductionFiniteLengthStatement`
([RationalSupercuspidalInductionFiniteLengthStatement](RationalSupercuspidalInductionFiniteLengthStatement.md),
the finite-length part of Renard, Théorème VI.5.4) to the published
`RationalCuspidalExtractionInputsStatement`
([RationalCuspidalExtractionInputs](RationalCuspidalExtractionInputs.md)).
The target pair, the inputs pair and every pair they import are unchanged.

## `RationalSupercuspidalInductionFiniteLengthFromExtractionInputsStatement`

At universes `u` and `v`,

```
RationalCuspidalExtractionInputsStatement.{u, v} →
  RationalSupercuspidalInductionFiniteLengthStatement.{u, v}
```

The target's input carrier universe `uV` is `v`; `u` and `v` are independent.

The antecedent is Worker 4358's published conjunction of two inputs, at the
binders of `RationalCuspidalJacquetFactorExtractionStatement.{u, v}` (every
nonarchimedean local field `k : Type u`, connected reductive `G`, actual
maximal split torus `i`, generic `ν`, `pointTopology` with local compactness,
nonarchimedean-group and T2 instances, and the premises `hStandard`, `hInter`,
`hRoots`, `hN`, `hZ`, `hU`, `hM`):

- (G) for some actual point Coxeter system `cs` with
  `RootLengthComparison i ν hN hZ cs`, every actual induced Jacquet object
  `r_J (i_I σ)` (carrier `max (u + 1) v`) has a finite zero-to-full filtration
  whose grades are actually isomorphic to actual normalized geometric terms
  `geometricTermFunctor … J I n hs ht` at minimal representatives;
- (E) inside each standard Levi, proper standard normalized induction has no
  irreducible `IsLeviCuspidal` subquotient.

The consequent is the unchanged target: for every actual standard index `I`
and every irreducible smooth complex `σ` of `levi i ν I` with carrier `v` that
satisfies `IsLeviCuspidal`, the full-parabolic Haar-normalized induction of `σ`
has finite length. The target's binders, including its structural premises
and all standard indices, are those of the published target; the implication
adds no premise to it.

## Intended proof and provenance

This is a derived (internal) reduction, not a quotation. It follows the proof
of the first assertion of Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
Théorème VI.5.4, printed pp.173–174 / PDF pp.179–180, with
Proposition VI.5.3 (ii), (iii), printed p.173 / PDF p.179. In Renard both
facts used there come from the geometric lemma VI.5.1 and Lemme VI.5.2, which
are exactly inputs (G) and (E).

The intended proof composes published results with one new step:

1. Detection. The published `rationalCuspidalJacquetFactorExtraction_of_inputs`
   turns the inputs into `RationalCuspidalJacquetFactorExtractionStatement`,
   and the published
   `rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
   turns that into `RationalSupportCategoryIrreducibleJacquetDetectionStatement`.
2. Associated Jacquet finite length (new). For root-associated `I`, `J` and an
   irreducible `IsLeviCuspidal` `σ`, every grade of the filtration (G) of
   `r_J (i_I σ)` has length at most one: when the source intersection is
   proper the geometric term vanishes (the published
   `PointCuspidalGeometricTermVanishing`), and when it is full the root
   association forces the inverse intersection to be full too, so the term is
   the irreducible conjugate of `σ` (the published full-intersection clause of
   `PointCuspidalExtractionGeometry`). Length is additive along the
   filtration, so `r_J (i_I σ)` has finite length. This is the finite-length
   part of VI.5.3 (iii) and gives `RationalAssociatedCuspidalJacquetFiniteLengthStatement`.
3. The published `rationalSupercuspidalInductionFiniteLengthFromInputs`
   ([RationalSupercuspidalInductionInputsProof](RationalSupercuspidalInductionInputsProof.md))
   combines 1 and 2 into the target.

Only input (G) is needed for step 2; input (E) enters through step 1.

## What remains open

This module proves nothing. Inputs (G) and (E) remain unproved in the Library;
the inputs Markdown records what each still needs. The implication is to be
proved in a separate proof unit.
