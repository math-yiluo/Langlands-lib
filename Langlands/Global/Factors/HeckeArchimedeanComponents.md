# Actual archimedean components and local presentation data

This internal derived module transports the proved real and complex character
presentations to the actual infinite completions used by the published Hecke
functional-equation statement. The number field remains in an arbitrary
universe. The actual completion ring equivalences and their isometries are
Mathlib's chosen real and complex equivalences, including its chosen complex
embedding.

`realCompletionCharacter` and `complexCompletionCharacter` precompose an actual
continuous quasicharacter of the completion units with the inverse equivalence
on units. The isometry gives continuity, including that of the inverse. The
proved standard-field constructors then define `realCompletionCharacterData`
and `complexCompletionCharacterData`. Applying the resulting data to the image
of a completion unit cancels the two inverse maps. The corresponding lemmas
therefore prove exactly the published `IsRealCharacterPresentation` and
`IsComplexCharacterPresentation`, for every supplied continuous character.

`infiniteAdditiveComponent` bundles the actual single-coordinate restriction
once its nontriviality has been proved. The real and complex additive transport
definitions precompose it with the inverse completion equivalence, which is
continuous and surjective, preserving nontriviality. The previously constructed
nonzero real Fourier scale and complex trace scale then define
`realCompletionAdditiveScale` and `complexCompletionAdditiveScale`. Their
specification lemmas cancel the inverse equivalences and prove the published
`IsRealAdditiveComponent` and `IsComplexAdditiveComponent` for the actual global
restriction. No completion, topology, Fourier sign or trace normalization is
changed.

`localData_of_pairing` proves the entire local-existence conjunct of the global
Hecke target conditional on a group homeomorphism from the actual additive
adeles (retagged multiplicatively) to their full compact-open Pontryagin dual,
whose value is exactly `ψ(a*x)`. The published local nontriviality lemmas use
injectivity of that pairing to prove every single-coordinate restriction
nontrivial. The finite local-data result supplies the finite characters and
self-dual Haar measures; the constructions above supply the infinite scales
and the real and complex quasicharacter presentations.

The pairing equivalence remains an explicit hypothesis here. This module does
not prove adelic self-duality, derive it from diagonal triviality, or prove any
Euler-product or global analytic conclusion. It assumes no functional equation
or character-classification certificate. Its provenance is direct transport of
the earlier proved constructors through Mathlib's actual completion
equivalences, followed by assembly of the previously proved conditional local
nontriviality and Haar-existence results.
