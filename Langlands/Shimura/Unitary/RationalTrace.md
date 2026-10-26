# The source-normalized rational trace of the Harris algebra

For the actual central simple CM algebra A of degree n in
`CentralSimpleUnitaryData`, `rationalTrace` constructs the rational linear
functional

    t(a) = (1/n) Tr_Q(L_a).

It uses the given algebra, not a supplied functional. The degree satisfies
n > 1. The construction is independent of a choice of signature charts.
This file also proves cyclicity and invariance under the datum's involution.

## The normalization in real coordinates

Let C be any `HarrisSignatureCharts` for this datum, with its actual
center-compatible matrix equivalences at the real embeddings of E. The
theorem `rationalTrace_real_coordinates` proves

    t(a) in R = 2 sum over tau:E -> R of Re(tr(C.evaluation(a)(tau))).

The coefficient 1/n is essential. The real regular representation of
M_n(C) has trace 2n times the real part of ordinary matrix trace. The
published actual real algebra splitting turns the rational real scalar
extension of A into the product of those matrix algebras. Trace is
unchanged by scalar extension and algebra equivalence, and sums over
products. Therefore the regular trace of a is n times the displayed
right-hand side. Cancellation of nonzero n proves the normalization.

`rationalTrace_unique` proves equality, as rational linear maps, of any
functional with this matrix-coordinate formula and the constructed t.
This also makes the normalized value independent of the chosen charts.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Section I.6, printed p.45 (PDF p.53), defines tr_(C/L)
as reduced trace to the center followed by center trace to L. In a split
central simple algebra, reduced trace is ordinary matrix trace. The two
complex embeddings above each real embedding contribute conjugate
matrix traces, whose sum is twice the real part. Thus the proved
coordinate formula has precisely that source normalization in the Harris
setting. The implementation constructs the rational-valued composite
directly; it does not construct a separate center-valued reduced-trace
map or a reduced-trace API for arbitrary central simple algebras.

## Intrinsic proofs

The auxiliary theorem `Langlands.Algebra.regularTrace_one_tmul` proves
compatibility with scalar extension by identifying multiplication by
1 tensor a with scalar extension of L_a and applying Mathlib's trace
base-change theorem. It assumes a finite free scalar module.

The auxiliary theorem
`AlgebraInvolution.regularTrace_apply_involution` works for a
finite-dimensional simple algebra over any characteristic-zero field.
Conjugation by the linear equivalence underlying the involution
identifies left multiplication by the involution of a with right
multiplication by a. The regular-trace duality theorem compares the
left and right traces. This proves involution invariance without
assuming that equality. Cyclicity and involution invariance pass to t
by multiplication by 1/n.

This is a derived implementation of the source's trace convention using
regular-trace duality, the real splitting, and matrix trace
calculations. It does not yet construct the alternating beta pairing,
its adjoint involution, or the identification of its similitudes.
