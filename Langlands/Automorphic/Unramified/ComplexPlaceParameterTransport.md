# Complex-place parameter transport and sums over actual places

This module supplies three internal definitions in
`Langlands.Automorphic.Unramified` for the B7 compatibility statement
`CyclicWeakBaseChangeComplexPlaceStatement`.
The field universes `uF` and `uE` are independent. Each definition takes
`{F : Type uF} {E : Type uE}`, `[Field F] [Field E]`,
`[NumberField F] [NumberField E]`, and `[Algebra F E]`. There is no
Galois, prime-degree, or totally complex hypothesis.

## Sources and provenance

The registered operator note
`operator-external-inputs-plan-2026-11-16`, *Formalizing the large external
inputs of the local Langlands correspondence for GL_n* (16 November 2026),
Section 2.2 B7, Section 4.6 “Interface,” and Section 4.8 “The infinity type,”
asks for compatibility of weak cyclic base change at complex places and the
corresponding Langlands sum for induction. Its original source is
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), registered as `arthur-clozel-1989-base-change`,
Chapter III, Theorem 5.1, printed p.212 / PDF page 226. That theorem promotes
weak lifting to strong lifting for representations induced from cuspidal
ones, under the assumptions of Theorem 4.2.

These sources motivate that compatibility statement. The three definitions
here are internal list vocabulary, rather than statements transcribed from
those sources. Their selected-coordinate convention comes from the existing
actual completion-map comparison in
`Langlands.Global.Arithmetic.HarrisDatumArchimedean`:
`Langlands.Global.HarrisDatum.extensionEmbedding_completionMap_of_eq`
and `Langlands.Global.HarrisDatum.extensionEmbedding_completionMap_of_ne`.
These comparison theorems have no totally complex hypothesis.

## Actual places and selected coordinates

Fix a complex place
`v : {v : NumberField.InfinitePlace F // v.IsComplex}`.
The index type is the existing
`Langlands.Global.AdelicFunctoriality.InfinitePlacesAbove E v.1` from
`Langlands.Global.AdelicFunctoriality.Norm`. Its elements are actual infinite
places of `E` together with the assertion that they lie above `v.1`; its
existing instance supplies the `LiesOver` hypothesis.

`complexPlaceAbove v w` has underlying place exactly `w.1`. It packages that
place with
`NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 v.2`.
Its result is the same complex-place subtype used by the existing
`OperatorRealization.HasComplexPlaceParameter` in
`Langlands.Automorphic.ArchimedeanPlaceParameter` and its isomorphism-class
and cuspidal wrappers, including
`PositiveRankCuspidalClass.HasComplexPlaceParameter` in
`Langlands.Automorphic.ArchimedeanPlaceParameterClasses`.
This changes only the packaging of the actual place.

The embeddings selected by the Library at `v.1` and `w.1` need not restrict
to each other. Put

```text
h : w.1.embedding.comp (algebraMap F E) = v.1.embedding.
```

In the `h` case, the existing completion-map theorem gives

```text
extensionEmbedding w.1 (LiesOver.completionMap x) = extensionEmbedding v.1 x.
```

In the other case, the other theorem gives

```text
extensionEmbedding w.1 (LiesOver.completionMap x) = star (extensionEmbedding v.1 x).
```

The dichotomy is justified by Mathlib's
`NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq`.
Thus the existing completion map, when read in these selected complex
coordinates, is identity or conjugation according to exactly the test `h`.
This module defines no second embedding lift, infinite-place subtype,
completion map, or complex character.

## Transport in either direction

For `ds : List Langlands.LocalFactor.Archimedean.ComplexCharacterData`,
`complexPlaceParameterTransport v w ds` is `ds` in the `h` case and
`ds.map ComplexCharacterData.conj` otherwise.
The conjugate operation is the existing one from
`Langlands.LocalFactor.ArchimedeanPairFactor`: it precomposes the actual
character with complex conjugation, negates its integer weight, and retains
its complex exponent. It is not complex conjugation of the character's value.

For transport from `w` to `v`, a character expressed in the selected
`w` coordinate is precomposed with the completed inclusion of `F_v` into
`E_w`; the formulas above give exactly this identity/conjugation rule.
For transport from `v` to `w`, the inverse coordinate change uses the same
rule because identity and conjugation are their own inverses. This explains
both uses of the one list formula; the module adds no separate theorem
about involutivity or compatibility of automorphic representations.
In both directions the operation keeps list positions and all occurrences
of blocks: it neither sorts nor removes repetitions.

## Enumeration and the list sum

For a supplied natural number `d`, an enumeration
`e : Fin d ≃ InfinitePlacesAbove E v.1`, and a family
`ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData`,
`complexPlaceLanglandsSum v e ds` is exactly

```text
(List.ofFn (fun i : Fin d =>
  complexPlaceParameterTransport v (e i) (ds (e i)))).flatten.
```

Each input list is read from the selected coordinates at its actual place
of `E` into those at `v`, and the lists are concatenated in the order
`e 0, e 1, …`. Because `e` is an equivalence, every actual place above `v`
is used exactly once; an arbitrary list of places could omit or repeat one.
No equality `d = Module.finrank F E` is assumed or needed. A later
cyclic-extension statement may specialize the enumeration.

The literal resulting list order depends on `e`, and the order within
each transported input list is retained. All occurrences, including repeated
blocks within or across places, remain in the result. The intended
Langlands interpretation retains these multiplicities and disregards
the list order. No representation-level permutation invariance is asserted
or proved here.

The sum is a list of parameter blocks. The module constructs no automorphic
representation and asserts no parameter existence, base-change or induction
compatibility, or bridge from these actual complex-place parameters to the
Library's infinitesimal-character predicate for regular algebraicity.
