# Special-fibre section embeddings under an isomorphism on global functions

Let `f : X → Y` be an actual morphism over a DVR `R`, with `X → Spec R`
smooth and `Y` affine. If the actual map `Γ(Y, O_Y) → Γ(X, O_X)` is bijective,
then the actual base change of `f` along the quotient residue field induces
an injective map on global functions. `sectionEmbedding` constructs this
embedding with its exact underlying section map.

There is no affineness, separatedness, quasi-compactness, connectedness or
henselianity assumption on `X`, and no smoothness, flatness or finite-type
assumption on `Y`. The fibres are the actual scheme pullbacks along
`Spec(R/𝔪) → Spec R`; no quotient-coordinate presentation of their section
rings is substituted for these schemes.

## Implemented proof and provenance

This is an internal consequence of the published smooth-DVR global
uniformizer division helper. A global function on `Y_s` lifts to a global
function on `Y`, because `Y_s → Y` is a closed immersion and `Y` is affine.
If its image under `f_s` is zero, its image on `X` vanishes pointwise on
`X_s`. Global uniformizer division writes that function as `πg`. The
bijection on global functions lifts `g` back to a function on `Y` and shows
that the original lift is itself divisible by `π`. The uniformizer maps to
zero in the actual quotient-residue fibre, so the original special-fibre
function is zero. In particular this step does not require the special
fibre of `Y` to be reduced.

The intended application is the canonical affinization map: it has an
isomorphism on global functions by the existing spectrum adjunction.
This module constructs no group law and assumes no affineness of the
original smooth scheme.
