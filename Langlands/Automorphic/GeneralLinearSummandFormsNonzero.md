# Nonzero cuspidal forms attached to irreducible cuspidal summands of `GL_n`

Module `Langlands.Automorphic.GeneralLinearSummandFormsNonzero`. This module assumes
`GroupSchemeQuotientL2ContinuousRepresentativeStatement` (continuous representatives for compact
convolution on the positive rational quotient, with a pointwise bound). From it, the module
derives `GeneralLinearSummandFormsNonzeroStatement`. With the Library reduction
`generalLinearSummandFormsDenseOfNonzero` it then derives `GeneralLinearSummandFormsDenseStatement`
(module `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction`). The module does
not prove the continuous-representative statement.

## Setting

`F` is a number field with compact adele quotient and `GL_{r+1}` is the general linear group
scheme. `Q` is the positive-central rational quotient for a central split torus `T` with
injective, finite-index character restriction. `S` is the full almost-everywhere cuspidal
subspace of `L²(Q, μQ)` and `πc` its right action. `P` is a nonzero closed `πc`-invariant
submodule of `S`, minimal among such submodules, and `A = P.map S.subtype` is its image in
`L²(Q, μQ)`.

## Definitions

- `matrixLevel F r K`: the open subgroup of `FiniteAdelicGL F (r+1)` corresponding to an open
  subgroup `K` of the finite adelic points, through `GeneralLinearGroupPoints.finiteHomeomorph`.
  `IsFiniteInvariant.matrixLevel` converts invariance under `K` into the invariance hypothesis of
  `exists_finiteSmooth_smoothing`, using `adelicHomeomorph_symm_ofFinite`.
- `compactFunctionAction F r`: right translation by the standard compact subgroup `K∞` on the
  matrix-model continuous functions `ContinuousRationalFunctions F (r+1)`.
- `classSubrepresentation`: the continuous functions that have an `L²` class
  (`IsGeneralLinearFormClass`), a subrepresentation for `K∞`
  (`IsGeneralLinearFormClass.compactFunctionAction`, from `IsGeneralLinearFormClass.rightTranslate`).
- `classMap`: the class map from that subrepresentation to `L²(Q, μQ)`, an intertwiner for
  `compactAction`. Classes are unique (`IsGeneralLinearFormClass.unique`). `classMap_injective`
  holds because a class determines the function (`generalLinearFormClass_form_eq`).
  `classInclusion` is the inclusion of the subrepresentation.

## Results

- `isInfiniteFinite_of_isGeneralLinearFormClass`: if the class of a continuous function is
  `K∞`-finite, that is, its orbit under `compactAction` spans a finite-dimensional space, then the
  function is `K∞`-finite (`IsInfiniteFinite`): its right translates by `K∞` span a
  finite-dimensional space. Neither notion requires a finite orbit. The injective class map
  reflects finite-dimensionality of orbit spans (`isFiniteVector_map_iff`), and the inclusion
  preserves it.
- `centerAction_slice_eq_zero`: if the enveloping derivative of a finite-smooth function by a
  central element has class zero, that element kills every slice.
- `summandForms_ne_bot_of_regular`: let `u` be a regular vector of `A` (`IsRegularVector`),
  invariant under a compact open subgroup `K` and `K∞`-finite. Let `ν` be a Haar measure
  on the archimedean group, right invariant under `K∞`. Then
  `summandForms F r T i A ≠ ⊥`. Construction:
  1. `exists_smoothedClass_ne_zero` gives a kernel `κ`, invariant under conjugation by `K∞`, with
     `smoothedClass … 1 κ u ≠ 0`.
  2. `exists_finiteSmooth_smoothing`, applied to the representative `h` of `u` and to
     `matrixLevel F r K`, gives a finite-smooth function `f`. Its enveloping derivatives are the
     pullbacks of the smoothed functions. `f` has class `smoothedClass … 1 κ u`, which lies in `A`
     (`smoothedClass_mem`).
  3. `f` is an automorphic form, by `isAutomorphicForm_iff_source_conditions`. Its finite level
     comes from its finite-smooth carrier. `K∞`-finiteness comes from
     `isFiniteVector_smoothedClass` and the class transfer above. The centre ideal of
     `exists_ideal_smoothedClass_eq_zero` kills `f`, because the corresponding smoothed classes
     vanish. Polynomial growth on each finite slice follows from
     `quotientMassBound_weightedQuotientOrbitIntegral` and `QuotientMassBound.sliceGrowth`.
  4. `automorphicOperatorCore_eq` makes `f` a stable automorphic function. It is cuspidal by
     `groupSchemeFullAEL2ContinuousCuspidality` and `mem_normalizedGeneralLinearParabolicCuspidal_iff`,
     since its class lies in `S`.
  5. If the attached forms were `⊥`, `f` would be zero and its class would vanish
     (`IsGeneralLinearFormClass.unique`), a contradiction.
- `summandForms_ne_bot_of_compactFinite`: the same conclusion for the Borel Haar measure. That
  measure is right invariant under `K∞` by `map_mul_right_eq_self_of_isCompact`.
- `generalLinearSummandFormsNonzero_of_representative`: the continuous-representative statement
  implies `GeneralLinearSummandFormsNonzeroStatement`. Starting from a nonzero vector of `P`,
  three results supply the vector needed above: `exists_isRegularVector_convolution`,
  `exists_isRegularVector_level` and `exists_isRegularVector_compactFinite`.
- `generalLinearSummandFormsDense_of_representative`: the continuous-representative statement
  implies `GeneralLinearSummandFormsDenseStatement`, by `generalLinearSummandFormsDenseOfNonzero`.

## Provenance

The statement `GeneralLinearSummandFormsDenseStatement` is the Library's single-summand density
consequence of Lemma 9.7.2 and the comparison (9.40) in the proof of Theorem 9.7.3, in Getz and
Hahn, *An Introduction to Automorphic Representations* (2024), printed pp. 264–266 (PDF
pp. 276–278). Lemma 9.7.2 obtains density of `K`-finite vectors in an irreducible unitary
representation through its factorization into archimedean and finite parts, by Proposition 4.4.7
and Lemma 5.3.7. It recovers each `K`-finite vector by a compact convolution. For (9.40) the book
places the `K`-finite vectors of `L²_cusp(π)` in the automorphic forms through the proof of
Theorem 6.6.4. It then shows that they are cuspidal by Lemma 9.2.3, which compares vanishing of
periods almost everywhere with vanishing after compact convolution, together with the
convolution recovery of Lemma 9.7.2.

The construction in this module is internal to the Library and differs from the book. A nonzero
vector of `P` is convolved to get a continuous representative with a conjugate subgroup mass
bound. The bound comes from the continuous-representative statement, here a hypothesis, and
from `GroupSchemeQuotientMassBound`. The vector is then averaged over a compact open subgroup of
the finite adelic points to give finite level. Next it is averaged against a continuous weight
on `K∞` with finite-dimensional left-translation span. This step is analogous to the
matrix-coefficient averaging in the proof of Proposition 4.4.7, printed pp. 116–118 (PDF
pp. 131–133). Finally it is smoothed by an archimedean kernel invariant under conjugation by
`K∞`. Pointwise cuspidality of the resulting form comes from the Library's
`groupSchemeFullAEL2ContinuousCuspidality`. That theorem compares almost-everywhere cuspidality
of a class with pointwise cuspidality of a continuous representative; the book makes the
corresponding comparison with Lemma 9.2.3. Finiteness of the centre action comes from the
unitary Schur argument of `GeneralLinearHilbertCenterFinite`, not from admissibility. Moderate
growth on each finite slice comes from the conjugate mass bound of
`GroupSchemeQuotientMassBound`.
