# Actual supercuspidal induction finite length from the cuspidal extraction inputs

Author: Worker 4238.

Module `Langlands.Representation.Aubert.General.RationalSupercuspidalInductionExtractionInputsProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

The theorem `rationalSupercuspidalInductionFiniteLengthFromExtractionInputs`
proves the published implication
`RationalSupercuspidalInductionFiniteLengthFromExtractionInputsStatement.{u, v}`
([RationalSupercuspidalInductionExtractionInputsStatement](RationalSupercuspidalInductionExtractionInputsStatement.md)):

```
RationalCuspidalExtractionInputsStatement.{u, v} →
  RationalSupercuspidalInductionFiniteLengthStatement.{u, v}
```

It does **not** prove the target `RationalSupercuspidalInductionFiniteLengthStatement`
itself: its antecedent, Worker 4358's published conjunction of the geometric
filtration input (G) and the proper-standard exclusion input (E)
([RationalCuspidalExtractionInputs](RationalCuspidalExtractionInputs.md)), is
still unproved in the Library. The universes `u` and `v` are independent, and
no premise is added to the target. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof outline

The final theorem is a composition of three results:

1. Detection. The published `rationalCuspidalJacquetFactorExtraction_of_inputs`
   turns the inputs into `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`,
   and the published
   `rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
   ([RationalIrreducibleJacquetFactorDetection](RationalIrreducibleJacquetFactorDetection.md))
   turns that into `RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}`.
2. Associated Jacquet finite length. The new theorem
   `rationalAssociatedCuspidalJacquetFiniteLength_of_extractionInputs` proves
   `RationalAssociatedCuspidalJacquetFiniteLengthStatement.{u, v}`
   ([RationalSupercuspidalInductionInputsStatement](RationalSupercuspidalInductionInputsStatement.md))
   from input (G) alone. It is described below.
3. The published `rationalSupercuspidalInductionFiniteLengthFromInputs`
   ([RationalSupercuspidalInductionInputsProof](RationalSupercuspidalInductionInputsProof.md))
   takes 1 and 2 to the target. That theorem lifts the target's input `σ` to
   carrier `max (u + 1) v`, applies the exact-family length criterion to the
   finitely many associated normalized Jacquet functors, and descends.

## Associated Jacquet finite length from the geometric filtration

This is the finite-length part of Renard, Proposition VI.5.3 (iii), for an
irreducible cuspidal `σ`, on the actual standard families.

`rationalAssociatedCuspidalJacquetFiniteLength_of_extractionInputs` introduces
the binders of `RationalAssociatedCuspidalJacquetFiniteLengthStatement` in the
same way as the published `rationalCuspidalJacquetFactorExtraction_of_inputs`:
the affine and monomorphism instances from `hG` and `hi`, `pointTopology`, and
the enumeration `simpleRelativeRootFintype`. It then takes standard indices
`I`, `J`, a rational point `n` with `rootAssociation i ν hN hZ I J n`, and an
irreducible `σ` of `levi i ν I` (carrier `max (u + 1) v`) satisfying
`IsLeviCuspidal`. From the inputs it extracts a Coxeter system `cs` with the
root-length comparison and the filtration input (G); input (E) is discarded.
The published `positiveSimpleReflectionComparison_of_rootLength` and
`pointCuspidalExtractionGeometry_of_rootComparisons` give
`PointCuspidalExtractionGeometry` for `cs`. Input (G) at `I`, `J`, `σ` gives
a finite zero-to-full filtration `s` of the actual `r_J (i_I σ)` whose grades
are actually isomorphic to actual normalized geometric terms. The theorem
`pointAssociatedCuspidal_hasFiniteLength_of_geometricGrades` then concludes.

`pointAssociatedCuspidal_hasFiniteLength_of_geometricGrades` is stated for an
arbitrary smooth representation `A` of `levi i ν J` with such a filtration,
as the published `pointCuspidalJacquetFactor_of_geometricFiltration` is. It
converts `IsLeviCuspidal` to the equivalent `IsCorollaryLeviCuspidal` with the
published `isCorollaryLeviCuspidal_iff_isLeviCuspidal`, and shows that every
grade has length at most one (`repLength`, the module length over the group
algebra). The grade is isomorphic to a geometric term at a minimal
representative `w` with normalizer lift `m`, and length is invariant under
this isomorphism (`repLength_congr`). There are two cases.

- Proper source intersection, `intersectionSubset cs J I w ≠ I`
  (`pointAssociatedCuspidalGeometricTerm_repLength_le_one_of_proper`). The
  vanishing clause of `PointCuspidalExtractionGeometry`
  (`PointCuspidalGeometricTermVanishing`) makes the term zero for the
  cuspidal `σ`, so its length is `0` (`repLength_eq_zero_iff`).
- Full source intersection, `intersectionSubset cs J I w = I`
  (`pointAssociatedCuspidalGeometricTerm_repLength_le_one_of_full`). The new
  lemma `intersectionSubset_inv_eq_of_rootAssociation` shows that the inverse
  intersection `intersectionSubset cs I J w⁻¹` is then all of `J`. By the
  published `intersectionSubset_eq_simpleImage_inter` at `w` and at `w⁻¹`
  (minimal by `isMinimal_inv`), the two intersections are
  `simpleImage cs w⁻¹ J ∩ I` and `simpleImage cs w I ∩ J`. These have the same
  cardinality (`card_simpleImage_intersections`), the first is `I`, and
  `I.card = J.card` by `rootAssociation_card_eq`. So the second is a subset of
  `J` of cardinality `J.card`, hence equal to `J`. With both intersections full,
  the last clause of `PointCuspidalExtractionGeometry` gives a membership
  witness `hConj` and an actual isomorphism of the geometric term with the
  conjugate `(conjugationFunctor m hConj).obj σ`. The generic lemma
  `repLength_le_one_of_iso_conjugation` shows that anything isomorphic to a
  conjugate of an irreducible representation has length at most one: the
  conjugate is irreducible by `Langlands.isIrreducible_comp_continuousMulEquiv_iff`
  and has length one by `repLength_eq_one_iff`.

The root association of the statement is used only through
`rootAssociation_card_eq`; the conjugating point of a grade is the normalizer
lift supplied by input (G), not `n`.

Finally the generic lemma `smooth_hasFiniteLength_of_filtration_grades_le_one`
turns the grade bound into finite length: length is additive along the
filtration (`repLength_eq_sum_of_filtration`), so the length of `A` is at most
the number of grades `r`, which is finite, and `Module.length_ne_top_iff`
gives `SmoothRep.HasFiniteLength`.

The two generic lemmas are stated over an abstract topological group and
subgroups. Proving the conjugate irreducibility directly at the rational
Levi subgroups made the kernel check time out.

## Relation to the source

Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
Proposition VI.5.3 (iii), printed p.173 / PDF p.179, gives a filtration of
`r_Q^G i_P^G ρ` with successive quotients the conjugates `wρ` for associated
standard Levis. The implemented argument uses the actual filtration of
input (G), whose grades are indexed by minimal representatives and may
repeat, and does not identify which grades are nonzero beyond the bound
"length at most one". Only finite length is concluded; no count of Weyl
cosets is asserted. Cuspidality is the target's proper-standard
`IsLeviCuspidal`, and association is the actual `rootAssociation`, as in the
published statements.

## What remains open

Inputs (G) and (E) of `RationalCuspidalExtractionInputsStatement` are unproved
in the Library; the inputs Markdown records what each still needs. Until both
are proved, the target `RationalSupercuspidalInductionFiniteLengthStatement`
remains open.
