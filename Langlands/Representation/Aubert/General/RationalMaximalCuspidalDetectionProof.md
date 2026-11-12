# Maximal-Levi Jacquet detection from cuspidal factor extraction

Author: Worker 3915.

`Langlands.Aubert.General.RationalPointFamily.rationalMaximalCuspidalJacquetDetectionFromExtraction`
proves the whole proposition
`RationalMaximalCuspidalJacquetDetectionFromExtractionStatement.{u, v}` from
`Langlands.Representation.Aubert.General.RationalRankOneLengthInputsStatement`.
It introduces no theorem parameters outside that proposition, and the
universes `u` and `v` stay independent. The statement pair and every pair it
imports are unchanged.

The proposition is an implication. Assuming
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}`, it concludes
`RationalMaximalCuspidalJacquetDetectionStatement.{u, v}`. This proof does not
prove the extraction proposition, whose separate proof task is
`e6add7c5-44c5-45ea-afe9-7f48c98fb927`.

## The argument

The proof introduces the binders of the detection statement exactly as
stated. As there, it installs `pointTopology`, the enumeration
`simpleRelativeRootFintype` and classical `DecidableEq`. It then takes a
maximal standard `J`, an irreducible inside-Levi cuspidal `σ` on
`levi i ν J`, and an actual irreducible subquotient `D` of the actual
normalized induction `i_J σ`.

1. The published proof `rationalWeylComparison` gives both comparisons
   `HasPointNormalizerComparison i` and `HasPointCentralizerComparison i` for
   the supplied maximal split torus. They are needed only to instantiate the
   extraction proposition.
2. Irreducibility of `D` makes its group-algebra module simple, hence
   nontrivial (`IsSimpleModule.nontrivial`).
3. The published `exists_irreducible_cuspidal_jacquet_subquotient` gives a
   standard index `I` with `r_I D` nontrivial. It also gives an actual
   irreducible representation `τ` of `levi i ν I` that satisfies
   `IsLeviCuspidal` and is an actual subquotient of `r_I D`.
4. The published `isCorollaryLeviCuspidal_iff_isLeviCuspidal` converts the
   cuspidality of `σ` from the zero-object form `IsCorollaryLeviCuspidal` to
   the subsingleton form `IsLeviCuspidal`. The two forms describe the same
   inside-Levi Jacquet modules.
5. The extraction proposition, at the same data and the comparisons from
   step 1, is applied to source `J`, target `I`, `σ`, `π = D` and `τ`. It
   returns a rational point `n` with `rootAssociation i ν hN hZ J I n`. Its
   Levi comparison and isomorphism conclusions are not used.
6. The published `rootAssociation_isMaximalStandard` shows that an actual root
   associate of the maximal standard `J` is maximal standard. So
   `I = Finset.univ.erase β` for some label `β`. With this `β`, step 3 gives
   the nontriviality of `r_(univ.erase β) D`.

## Dependencies

The proof uses these published declarations: `rationalWeylComparison`,
`exists_irreducible_cuspidal_jacquet_subquotient`,
`isCorollaryLeviCuspidal_iff_isLeviCuspidal` and
`rootAssociation_isMaximalStandard`, together with the standard-family
adapters `isSemidirectDecomposition_of_standardCocharacterStatement` and
`isSemidirectDecomposition_in_levi`.

- `rationalWeylComparison` uses the infinitude of a nontrivially valued field
  and the published normalizer and centralizer comparison for split tori over
  infinite fields.
- `exists_irreducible_cuspidal_jacquet_subquotient` uses the published
  minimal-Jacquet construction, the existence of irreducible subquotients
  without finite length, and compact-limit radicals from
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
- `rootAssociation_isMaximalStandard` uses only the cardinality and properness
  laws of actual root association.

The proof body invokes no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem. The geometric lemma
and proper-induction exclusion enter only through the hypothesis
`RationalCuspidalJacquetFactorExtractionStatement`.

The checked lean_check diagnostic `9b2d0f45-2cb8-4ad5-a615-f99182620d86`
reports zero errors and warnings and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
