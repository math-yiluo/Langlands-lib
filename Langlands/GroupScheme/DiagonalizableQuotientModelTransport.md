# Transport of direct diagonalizable quotient models

Worker 587. Internal derived transport for Task 7326.

`AffineDiagonalizableModelQuotientStatement` asserts quotient existence for
an affine group over `Spec R` with a specified closed normal inclusion of
`Diagonalizable.groupScheme R M`, where the abelian group `M` is finitely
generated. The quotient is affine over `Spec R` and its projection has the
full fppf kernel specified by the inclusion. This proposition remains an
explicit premise in this module.

The first theorem converts this premise to the affine-scheme interface
`AffineDiagonalizableNormalQuotientStatement`. For an affine scheme `S`,
pull back along its canonical isomorphism `Spec Γ(S, ⊤) → S`. A witness for
diagonalizability identifies the pulled-back kernel with a relative
diagonalizable group; the published diagonalizable base-change isomorphism
identifies that group with the direct ring model. Precomposing the inclusion
with the inverse isomorphism preserves closedness and its full range.
Apply the assumed model construction, then descend the affine quotient
along the canonical base isomorphism using effective affine quotient descent.

The second theorem combines this transport with the arbitrary-base
multiplicative-type quotient reduction. Its conclusion is the unchanged
published central multiplicative-type quotient target, conditional on the
direct ring-model premise. No proof of that premise is claimed here.

All content is derived from published Library constructions and the paired
conditional arbitrary-base reduction; no new literature assertion is used.
