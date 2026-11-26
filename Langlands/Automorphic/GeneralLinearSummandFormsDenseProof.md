# Density of the forms attached to an irreducible cuspidal summand of `GL_n`

Module `Langlands.Automorphic.GeneralLinearSummandFormsDenseProof`. It proves
`GeneralLinearSummandFormsDenseStatement` (module
`Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction`) as the theorem
`generalLinearSummandFormsDense`.

## Statement

The data and hypotheses are as follows.

- `F` is a number field whose additive adele quotient `𝔸_F / F` (`AdeleQuotient F`) is compact.
- `r` is a natural number, and `ParabolicDynamicStatement` is assumed.
- `T` is a commutative group scheme over `F`, and `i : T → GL_{r+1}` is a homomorphism.
- `i` is central, its character restriction is injective, and the image of that restriction has
  finite index.
- `e` identifies `T` with the split torus on a finite type `I`.
- Haar measure on the norm-one subgroup of the adelic points of `GL_{r+1}` is right invariant.

`S` is the full almost-everywhere cuspidal subspace of `L²` of the positive rational quotient,
and `πc` is its right action. Let `P` be a nonzero closed `πc`-invariant subspace of `S` whose
only closed `πc`-invariant subspaces are `0` and `P`. The statement says that every vector of
`P` lies in the closure, taken in `S`, of the set of vectors `y` of `S` that are classes of forms
attached to `P`. Such a `y` is the class of `f` in the sense of `IsGeneralLinearFormClass`, for
some `f` in `summandForms F r T i (P.map S.subtype)`.

- `summandForms F r T i A` consists of the stable automorphic functions
  (`StableAutomorphicFunctions`) whose matrix-model continuous function is cuspidal. That
  function must also have a class lying in `A`.
- `IsGeneralLinearFormClass F r T i φ f` asks for a continuous function `h` on the quotient. Its
  pullback to the adelic points, transported to the matrix model, must equal `f`, and `φ` must
  agree with `h` almost everywhere for the quotient Haar measure.

The forms follow the Library's Borel–Jacquet conventions. At each fixed finite coordinate a form
is smooth in the archimedean variable. It has finite level, is `K∞`-finite and is killed by an
ideal of finite codimension in the centre of the enveloping algebra. It also satisfies a growth
bound on each finite slice.

## Proof

The proof is a single application:
`generalLinearSummandFormsDense_of_representative groupSchemeQuotientL2ContinuousRepresentative`.

- `groupSchemeQuotientL2ContinuousRepresentative` (module
  `Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeProof`) proves
  `GroupSchemeQuotientL2ContinuousRepresentativeStatement`. Convolution with a compactly
  supported continuous weight sends every `L²` class of the positive rational quotient to a class
  with a continuous representative. That representative satisfies a bound at each coset by the
  subgroup mass of a conjugate compact set.
- `generalLinearSummandFormsDense_of_representative` (module
  `Langlands.Automorphic.GeneralLinearSummandFormsNonzero`) derives the density statement from
  that statement. It first shows that the forms attached to `P` are nonzero
  (`generalLinearSummandFormsNonzero_of_representative`). The Library reduction
  `generalLinearSummandFormsDenseOfNonzero` then upgrades this to density. It takes the closure
  of the set of attached classes, shows that it is `πc`-invariant, and applies minimality of `P`.
  The paired page `GeneralLinearSummandFormsNonzero.md` describes how a nonzero form is built.
  1. A nonzero vector of `P` is convolved by a compactly supported weight on the adelic group, to
     get a continuous representative with a conjugate mass bound.
  2. It is averaged over a compact open subgroup of the finite adelic points, to get finite
     level.
  3. It is averaged against a continuous weight on `K∞` whose left translates span a
     finite-dimensional space. Such a weight is chosen close to a normalized bump, so that the
     average is nonzero. The average is `K∞`-finite: its `K∞`-orbit spans a finite-dimensional
     space.
  4. It is smoothed by a smooth compactly supported archimedean kernel invariant under
     conjugation by `K∞`. This smoothing preserves `K∞`-finiteness and can be chosen nonzero.

  The result is a nonzero stable cuspidal form whose class lies in `P`. The ingredients sit in
  these modules:
  - `Langlands.Analysis.NormalizedAverageApproximation`: normalized averages and bumps;
  - `Langlands.Automorphic.GeneralLinearHilbertCenterFinite`: finiteness of the centre action
    on the smooth vectors of an irreducible unitary representation;
  - `Langlands.Automorphic.GeneralLinearSummandSmoothing`: archimedean smoothing;
  - `Langlands.Automorphic.GeneralLinearSummandCenterAnnihilation`: an ideal of finite
    codimension in the centre that kills the smoothed classes;
  - `Langlands.Automorphic.GroupSchemeQuotientMassBound`: conjugate mass bounds and growth on
    each finite slice;
  - `Langlands.Automorphic.GroupSchemeQuotientRegularVectors`: regular vectors at finite level;
  - `Langlands.Automorphic.GeneralLinearSummandCompactFinite`: `K∞`-finite averages and
    smoothing by kernels invariant under conjugation by `K∞`.

## Provenance

The statement is the Library's single-summand density consequence of Lemma 9.7.2 and the
comparison (9.40) in the proof of Theorem 9.7.3, in Getz and Hahn, *An Introduction to
Automorphic Representations* (2024), printed pp. 264–266 (PDF pp. 276–278). In the book,
Lemma 9.7.2 obtains density of `K`-finite vectors through the factorization of the
representation into archimedean and finite parts, and recovers each `K`-finite vector by a
compact convolution. The cuspidality of the `K`-finite vectors in (9.40) comes from Lemma 9.2.3,
printed p. 243 (PDF p. 255). The proof here is internal to the Library and does not follow the
book's sequence of steps. The `K∞`-finite averaging is analogous to the matrix-coefficient
averaging in the proof of Proposition 4.4.7, printed pp. 116–118 (PDF pp. 131–133). The
construction of actual forms and their slice growth come from the Library results named above.
The coset-wise mass bound comes from the Library theorem
`groupSchemeQuotientL2ContinuousRepresentative`. It is not the book's estimate (9.13), printed
pp. 247–248 (PDF pp. 259–260). That estimate is the uniform bound `‖R(f)φ‖_∞ ≪_f ‖φ‖₂` assumed in
the trace-class criterion of Lemma 9.3.3. Centre finiteness comes from a unitary Schur argument,
not from admissibility.
