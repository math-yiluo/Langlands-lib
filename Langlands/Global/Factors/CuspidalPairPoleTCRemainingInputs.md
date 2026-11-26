# The totally complex pole theorem from its functional-equation and complex inputs

This module expresses `Langlands.Global.CuspidalPairPoleTCStatement`, the form of the cuspidal
pair pole theorem (Getz–Hahn, Theorem 11.7.1; Cogdell 2004, Theorems 4.1–4.2) over totally
complex number fields, as a consequence of four named propositions, in the two original
universes `u` (number field) and `uQ` (factor universe of the spectral presentations). The
archimedean slice model is assumed only over totally complex fields. The complex restriction
surjectivity premise ranges over all number fields but concerns only their complex places.

## Statements

`CuspidalPairPoles.specifiedWhittakerSliceComparisonAt_of_complex` proves, for a totally complex
number field `F`, that `SpecifiedWhittakerSliceComparisonAt F` follows from the fieldwise slice
model `RankinSelbergGlobal.InfiniteWhittakerSliceModelAt F` (module
`InfiniteWhittakerSliceModelTCStatement`) and
`ComplexPlaceWhittakerRestrictionSurjectivityStatement`. The Library's
`specifiedWhittakerSliceComparisonAt_of_local` takes instead the all-field slice model
`InfiniteWhittakerSliceModelStatement` and also the real restriction surjectivity
`RealPlaceWhittakerRestrictionSurjectivityStatement`; over a totally complex field the type of
real places is empty, so the real-place range conditions are vacuous and that premise is not
needed.

`CuspidalPairPoles.CuspidalPairPoleTCRemainingInputsStatement.{u,uQ}` is the implication from

- `CuspidalPairCompletedEquationTCStatement.{u,uQ}`, the completed equation of cuspidal pairs
  over totally complex fields (module `CuspidalPairFunctionalEquationTCStatement`);
- `RankinSelbergGlobal.ComplexOrdinaryNormalizedGenerationStatement`, the complex ordinary
  generation conclusion of Jacquet's theory (module `ArchimedeanOrdinaryNormalizedTests`);
- `RankinSelbergGlobal.InfiniteWhittakerSliceModelTCStatement.{u,uQ}`, the archimedean
  Whittaker slice model `InfiniteWhittakerSliceModelAt F` at every totally complex field `F`;
- `ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u}`, surjectivity of the actual
  restrictions onto the complex coefficient models (module `CuspidalPairPoleLocalRanges`); it
  quantifies over all number fields and their complex places, and the proof applies it only
  over totally complex fields

to `CuspidalPairPoleTCStatement.{u,uQ}`. `cuspidalPairPoleTCRemainingInputs` proves it.

## Proofs

For `specifiedWhittakerSliceComparisonAt_of_complex`, the proof is that of
`specifiedWhittakerSliceComparisonAt_of_local` at the complex places. Choose slice model data
for the standard character `ψ` and for its inverse, obtain the actual place ranges from
`hasActualPlaceWhittakerRanges_of_cuspidal`, and prove each range equality by two inclusions:
an actual restriction lies in the complex coefficient model by
`archimedeanPlaceWhittakerModels`, and every model function is an actual restriction by the
complex surjectivity premise. The real-place range equalities are vacuous, because
`InfinitePlace.not_isReal_iff_isComplex` and `IsTotallyComplex.isComplex` show that no infinite
place of `F` is real.

`cuspidalPairPoleTCRemainingInputs` applies the Library's `cuspidalPairPoleTCFromLocalTests`
with the completed equation, the complex continuation and the complex strip growth (the two
components of the Library's `complexOrdinaryNormalizedAllGrowth`), the generation premise, and
the slice comparison above at every totally complex field, applied to the slice model premise
at that field.

The module does not prove any of the four premises.

## Provenance

This is an internal assembly along the route of the Library's `cuspidalPairPoleTCFromLocalTests`:
the ordinary global integrals of J. W. Cogdell, *Analytic theory of L-functions for GL_n*
(2004), §4, Theorems 4.1–4.2, printed pp. 219–222, with the archimedean theory of
`GL_n(ℂ)` in H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorems 2.1, 2.3, 2.6
and 2.7, author-posted pp. 6–10.
