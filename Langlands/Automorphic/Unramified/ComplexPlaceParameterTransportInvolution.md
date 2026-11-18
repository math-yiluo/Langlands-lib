# Reversing complex-place parameter transport

Worker 230 authored this elementary support lemma for B7. Its provenance is
internal: it computes the existing actual-character conjugation and the
identity/conjugation formula in
`Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport`.

The declaration
`Langlands.Automorphic.Unramified.complexPlaceParameterTransport_involutive`
has independent field universes `uF uE`. It quantifies
`{F : Type uF} {E : Type uE}`, `[Field F] [Field E]`,
`[NumberField F] [NumberField E]`, `[Algebra F E]`, an actual complex place
`v : {v : NumberField.InfinitePlace F // v.IsComplex}`, and an actual
`w : Langlands.Global.AdelicFunctoriality.InfinitePlacesAbove E v.1`.
It proves

```lean
Function.Involutive (complexPlaceParameterTransport v w)
```

Thus applying the same transport twice returns the original list, with the
same order and every multiplicity. The lemma needs no Galois, cyclicity,
prime-degree, compactness or totally complex hypothesis.

The implemented proof first establishes, privately, that
`ComplexCharacterData.conj` applied twice returns the complete original
character datum. Its character field is precomposed twice with the existing
`complexConjugation`; extensionality and conjugating a complex number twice
give the original actual character. Its integer weight is negated twice and
its exponent is unchanged. The remaining certification field is a proposition,
so proof irrelevance identifies the records once these data agree.

The main proof splits on
`w.1.embedding.comp (algebraMap F E) = v.1.embedding`.
In that branch, both transports are identity. In the other branch, both
are `List.map ComplexCharacterData.conj`; `List.map_involutive_iff` applies
the private character calculation to the list.

This computation uses the coordinate convention already justified by
`Langlands.Global.HarrisDatum.extensionEmbedding_completionMap_of_eq` and
`Langlands.Global.HarrisDatum.extensionEmbedding_completionMap_of_ne`:
the actual completed inclusion is identity or conjugation in the selected
coordinates. It introduces no new completion map or representation
comparison. Combined with a supplied B7 base-change equivalence, it permits
recovering a downstairs list from a known upstairs list. The lemma itself
makes no parameter-existence or automorphic-compatibility claim.

Composition along towers and transport through endpoint field equivalences
are separate structural obligations of the downstream branch proofs.
