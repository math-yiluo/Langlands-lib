# Determinant density on complex general linear groups

For any additive Haar measure \(\mu\) on the complex square matrix space,
`complexMatrixHaar` is Haar measure on the general linear group. Its
pushforward through the inclusion of the invertible locus is the density
\(\lvert\det X\rvert_{\mathbb C}^{-n}\) against \(\mu\), with
\(\lvert z\rvert_{\mathbb C}=\lVert z\rVert^2\).

The proof computes the real determinant of multiplication by a complex
scalar using the algebra norm. The generic rectangular change of
variables then gives the matrix left- and right-multiplication scaling.
The Library's determinant-density construction supplies Haar invariance
and local finiteness. The right-translation calculation uses the same
density cancellation. The singular-locus theorem, applied to complex
additive measure, removes the restriction to the invertible locus
from the pushforward formula.

This internal specialization provides the measure conversion for the
matrix integrals in Jacquet, *Archimedean Rankin–Selberg integrals*,
§3.2 and §4.7. The formula retains the supplied additive Haar measure.
