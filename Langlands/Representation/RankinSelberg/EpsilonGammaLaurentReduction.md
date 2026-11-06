# The epsilon-to-gamma reduction for Laurent-valued continuations

This derived module formalizes the algebraic part of the supercuspidal
unequal-rank epsilon-to-gamma reduction. Its provenance is the published
`RationalZeta`, `EpsilonFactor`, `DualModels`, and `UnequalRankGammaFactor` APIs.
It does not assert that the integrals of any specific representation have the
Laurent-valuedness property needed below.

`HasLaurentValues S` says that every rational function in `S` is the image of a
Laurent polynomial under the genuine Laurent embedding. An existing normalized
generator with polynomial `P` places the reciprocal of `P` in the span of `S`.
Multiplying by `P.toLaurent` shows that this span contains one. The proof uses
the nonvanishing of `P`, which follows from its normalization at zero.
Consequently `P = 1` whenever `HasLaurentValues S`: the normalized-generator
criterion first proves that one is another normalized generator of the same
span, then generator uniqueness identifies the polynomials. No additional
constant integral witness is required.

For a fixed pair of functionals, the unequal-rank epsilon relation supplies
common normalized polynomials for every rectangular block. Laurent-valuedness
of the original pair's block zero forces its polynomial to one.
Laurent-valuedness of block zero for the inverse-transpose pair at the negative
additive character forces the dual polynomial to one. In the latter comparison
the proof uses the epsilon equation at the opposite extreme block and the
published dual-model equality, which exchanges the block indices. The existing
epsilon-to-gamma equation comparison then applies, and its rational gamma
expression simplifies to the epsilon monomial.

`IsUnequalRankEpsilonFactor.gammaFactor_of_laurentValues` applies this argument
for each compatible quotient measure and each pair of nonzero functionals in
the universal relation. It yields the full universal gamma relation from the
epsilon certificate, provided the two block-zero Laurent-valuedness hypotheses
hold. It assumes neither intrinsic L-polynomial certificates nor a separate
analytic-conclusion certificate. The Laurent-valuedness hypotheses are still
substantial mathematical obligations. This module alone proves neither
supercuspidal L-factor vanishing nor local converse. All three universes are
independent.
