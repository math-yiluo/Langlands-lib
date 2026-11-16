# Signed reversal on mixed real standard modules

This internal construction restricts the signed pullback from
`RealMixedSwapSigned` to the actual mixed standard modules on `GL₃(ℝ)`.
Let `d` be a complex character datum, `b` a real character datum, and
`q = |d.weight| + 1`. Set `d′ = reverseInduced d` and
`b′ = reverseCharacter d b`, using the parameter conventions in
`RealMixedSwapParameters`. No weight, ordering, or unlinkedness hypothesis is
needed for the constructions here.

`inducedCharacterSignedEquiv d b` is a complex-linear equivalence between the
orthogonal-finite functions in the standard modules of `[induced d, character b]`
and `[character b′, induced d′]`. `characterInducedSignedEquiv d b` gives the
corresponding equivalence from `[character b, induced d]` to
`[induced d′, character b′]`. Each map and its inverse acts on underlying functions
by `f(g) ↦ sgn(det g)^q f(w(gᵀ)⁻¹)`, where
`w = [[0,0,1],[0,-1,0],[1,0,0]]`. The four coercion lemmas record these formulas.

The proof first specializes standard-module membership to principal-series
membership and vanishing of Fourier coefficients with `|k| < |d.weight|`. The
induction block starts at position zero in the induction-character list and at
position one in the character-induction list. The block-position rank bound
excludes every other position.

The position-character identities from `RealMixedSwapParameters` and the signed
principal-series transport establish the covariance and smoothness conditions.
The Fourier identity from `RealMixedSwapSigned` exchanges positions zero and one
without changing the integer Fourier index. The induction weight is unchanged,
so the same low coefficients vanish after transport. For the inverse covariance
condition, `signedReverseCharacters_inverse` applies the character identity at
the reversed position and inverse real unit; the two sign powers cancel by
`unitSign² = 1`. This proves inverse membership directly. Preservation of
orthogonal finiteness and the ambient signed involution then give the two linear
equivalences.

This is derived infrastructure for the mixed real swap proof, with provenance
in the imported definitions and previously proved signed reversal identities.
The equivalences alone do not assert an ordinary compact or Lie intertwiner;
the signed pullback has a determinant-sign factor under compact translation,
which a conjugation argument must account for.
