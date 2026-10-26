# Global differential base-change reduction

`Langlands.Scheme.relativeDifferentialsBaseChangeIsIso_of_local_inputs`
reduces the published proposition
`RelativeDifferentialsBaseChangeIsIsoStatement S` to two explicit inputs:
open-immersion locality of the canonical square map and canonical base change
for spectra of arbitrary commutative rings. The lemma is conditional; the
companion `RelativeDifferentialsBaseChangeIsIso` module supplies both inputs
by published proofs. All schemes and rings lie in arbitrary universe `u`.

The module imports the published `RelativeDifferentialsBaseChangeTransport`,
which supplies composition and congruence for the actual square maps and the
criterion detecting invertibility after pullback along an open cover.

The private lemma `baseChange_isIso_pullback_of_isIso` compares two
base-change diagrams whose maps on both sources and on the base are open
immersions. Write `l` for the induced map of their categorical pullbacks.
Composition and congruence express the pullback along `l` of the larger
base-change map, followed by the square map associated to `l`, as a composite
of pullback coherence isomorphisms, the pullback of the source comparison,
and the smaller base-change map. Open-immersion locality makes the two side
square maps invertible. If the smaller base-change map is invertible,
cancellation therefore proves invertibility of the pulled-back larger map.
This equality is about the canonical maps themselves, with the necessary
`pullbackComp` and `pullbackCongr` factors.

The reduction then has three steps. First,
`baseChange_isIso_of_affine` transports an arbitrary affine diagram to
spectra through the inverses of the canonical `isoSpec` isomorphisms.
Naturality gives both commutative squares. The spectral input applies to
the maps on global sections, and the preceding comparison lemma plus the
singleton isomorphism cover gives the affine result.

Second, `baseChange_isIso_of_affineBase` covers a diagram over an affine
base by the affine covers of both sources, using Mathlib's
`Scheme.Pullback.openCoverOfLeftRight`. Each local diagram is affine.
The comparison lemma identifies its base-change map with the restriction
of the original map, and the open-cover criterion gives invertibility.

Finally, `relativeDifferentialsBaseChangeIsIso_of_local_inputs` uses
`Scheme.Pullback.openCoverOfBase` for the affine cover of the base `S`.
Over each affine member, the two sources are the corresponding pullbacks,
so the affine-base lemma applies. Both projection squares commute by the
pullback identities and their vertical maps are open immersions. The
comparison lemma and the open-cover criterion finish the proof. Empty
schemes and zero coordinate rings require no separate assumptions.

This is an internal derived assembly from the published canonical maps,
transport identities, stalk criterion, and Mathlib's scheme-cover API.
Its mathematical route implements the affine-local passage in Stacks
Project Lemma 29.33.10 (tag [01V0](https://stacks.math.columbia.edu/tag/01V0)),
with the canonical map of Lemma 29.33.8 (tag
[01UV](https://stacks.math.columbia.edu/tag/01UV)). Both originals and their
proofs were read in registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, retained file
`01UM.html`, lines 321–371, directory content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
No relevant public erratum was present in the consulted Library.
Worker 208 authored this reduction.
