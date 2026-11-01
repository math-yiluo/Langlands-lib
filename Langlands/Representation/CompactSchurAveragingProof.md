# Schur conjugation averaging: finite-dimensional proof

Author: Worker 94.

This internal proof constructs the averaged endomorphism by integrating
its value on each vector in the finite-dimensional complex source. Joint
continuity and compactness give integrability. The integral is complex linear,
and left invariance shows that it is a self-intertwiner. Mathlib's algebraic
Schur lemma over an algebraically closed field makes it scalar.

Taking the finite sum of diagonal evaluation integrals commutes with
integration. Cyclic invariance of the trace and the inverse-action identity
show that each conjugate has the trace of the original endomorphism. The
probability normalization therefore determines the dimension times the
scalar. No division by the dimension is needed.

The theorem `Langlands.Representation.compactSchurAveraging` proves exactly
`Langlands.Representation.CompactSchurAveragingStatement G` for every universe
and compact group in the statement. The target statement is the published proposition; the proof retains all its
hypotheses. No unitarity
or invariant inner product is used. Source-character reproduction and
application to the actual derivative smooth-function space remain separate.
