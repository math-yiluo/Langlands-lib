# Boundedness from the spans of the actual simple factors

This internal assembly of the middle part of Kaletha–Prasad, Lemma 2.2.11
(printed pages 72–73, PDF pages 103–104), works over an algebraically closed
valuative field with an explicit group of actual rational points. It does not
assert density or full matrix span without hypotheses.

`SimpleFactorFamily.HasFullMatrixSpans F alpha` says that the matrices on the
family `alpha` span the full matrix algebra in each of the actual simple factors
of `F`. Pointwise coefficient integrality passes from the original representation
to each actual subquotient. The trace-probe family theorem then bounds its
entries, and the actual direct sum has bounded entries. This also handles empty
families and zero dimensions.

For a smooth affine group with trivial unipotent radical and a closed faithful
original representation, the factor sum is an actual finite morphism. The image
of a group family is inverse-stable. Its entry bounds therefore bound every
regular function on its image in the general linear group. Integral affine
pullback transports that bound to the original specified family of points. The
finite-map theorem handles the full scheme-theoretic kernel, without assuming
that kernel is smooth. The conclusion is exactly algebraic boundedness of the
range of `alpha`; the span and integrality assumptions concern that range only.

The pointwise subquotient inheritance and finite affine pullback helpers are by
Worker 1554; the simple-factor, finite-map and trace-entry assembly is by
Worker 1296.
