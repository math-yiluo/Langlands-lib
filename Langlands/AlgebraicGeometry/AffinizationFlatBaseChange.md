# Canonical affinization and flat affine base change

Worker 596.

Suppose that `P` is the actual pullback of `X → Z` along `Y → Z`, that `Y`
and `Z` are affine, that `Y → Z` is flat, and that `X` is quasi-compact and
quasi-separated. `isPullback_toSpecΓ` proves that the naturality square

```text
P ─────────────→ Spec Γ(P, O_P)
│                         │
│                         │ Spec(fst.appTop)
↓                         ↓
X ─────────────→ Spec Γ(X, O_X)
```

is cartesian. Both horizontal arrows are the actual canonical affinization
maps. `naturalityPullbackIso` is the resulting actual isomorphism from `P`
to the indicated pullback; its two projection formulas identify the
canonical map and the original pullback projection exactly.

## Implemented proof and provenance

This is an internal reusable extraction of the affinization-square argument
already implemented in `FieldExtensionAffineDescentProof` and
`FaithfullyFlatAffineDescent`. It uses the published flat-base-change theorem
`LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback`: the resulting
pushout of global section rings becomes a pullback of spectra. The
naturality square for `Y → Z` is cartesian because the canonical affinization
maps of its affine schemes are isomorphisms. Pasting with the supplied
pullback square and cancelling the spectra square gives the desired square.

No faithful-flatness, surjectivity, field, noetherianity, finite-type or
affineness assumption on `X` is used. This module constructs no group law.
