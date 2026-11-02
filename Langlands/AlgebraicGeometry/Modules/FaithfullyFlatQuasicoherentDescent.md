# Quasi-coherence detected by affine faithfully flat pullback

This internal result concerns the actual ordinary module categories of schemes
in an arbitrary universe `u`. If `p : X → Y` is affine, flat and surjective,
and the actual pullback `p*M` of an ordinary module `M` on `Y` is
quasi-coherent, then `M` is quasi-coherent. Combining this with the existing
preservation theorem gives an equivalence of these two quasi-coherence
predicates.

The proof uses the published flat pullback exactness and reflection of ordinary
module isomorphisms. They imply that pullback reflects equalizers. For the
actual pullback–pushforward adjunction, Mathlib's
`Comonad.ComonadicityInternal.unitEqualizerOfCoreflectsEqualizer` then realizes
`M` as the equalizer of

`p_*p*(η_M), η_(p_*p*M) : p_*p*M → p_*p*p_*p*M`.

Both terms are quasi-coherent: affine pushforward preserves quasi-coherence,
and arbitrary scheme pullback preserves quasi-coherence. In the preadditive
module category this equalizer is a kernel of the difference of the two maps.
The published quasi-coherent kernel closure result and invariance under the
actual isomorphism with that kernel establish the conclusion.

The provenance is internal. The argument combines the actual adjunction unit
equalizer, flat conservative pullback, affine pushforward and quasi-coherent
kernel closure; it assumes no geometric object descent or quasi-coherence
detection result. It does not assert finite presentation, relative flatness,
coherent-family stack descent or the coherent-stack atlas theorem.
