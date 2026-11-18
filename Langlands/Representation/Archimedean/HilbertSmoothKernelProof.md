# Proof of the Hilbert smooth-kernel criterion

`Langlands.Archimedean.hilbertSmoothKernel` proves
`Langlands.Archimedean.HilbertSmoothKernelStatement.{uA,uM,uH}` for arbitrary maps
from a smooth boundaryless manifold modelled on a finite-dimensional real normed
space to a complete complex inner-product space. This is the finite-dimensional
real-manifold specialization of Neeb's Theorem 7.1. [Neeb, *On Differentiable
Vectors for Representations of Infinite Dimensional Lie Groups*, arXiv:1002.1602v3,
pp. 21–23](https://arxiv.org/pdf/1002.1602v3).

The forward implication composes the smooth product of the given map with the
real-smooth complex inner product. For the converse, fix a chart, write `U` for
its open target, and compose the given map with the inverse chart to obtain
`g`. The real part of the pulled-back complex kernel is the real inner-product
kernel `K` of `g`. The real inner-product structure uses the given Hilbert norm.

For `x, y ∈ U` and directions `v, w`, the inner product of
`t⁻¹ • (g (x + t • v) - g x)` and `s⁻¹ • (g (y + s • w) - g y)` is the
rectangular divided difference of `K` along the two lines. Two scalar mean value
theorems express it as the mixed derivative near `(x, y)`. As the nonzero
parameters `t` and `s` tend independently to zero, the divided difference tends
to `D(DK)(x, y)(0, w)(v, 0)`. Taking `y = x` and `w = v` and comparing the
two individual squared norms with the mixed inner product shows that the
difference quotients are Cauchy in Hilbert norm. Completeness gives the
directional derivatives, and the joint limit identifies their inner products
with the mixed derivatives of `K`.

The mixed derivative is additive in its first direction. Pairing the defect
of additivity of the directional derivative with the three directional
derivatives that form the defect gives its squared norm as zero. Homogeneity
follows from rescaling the line parameter. For each fixed direction, the
directional derivative has a smooth real kernel given by the same mixed
derivative formula. The squared-distance identity gives continuity from
continuity of a real kernel, both for `g` and for each directional derivative.
Finite-dimensionality then gives operator-norm continuity of the resulting
family of continuous linear maps. Applying a norm mean value bound to the
remainder along each short segment gives the little-o estimate for the
Fréchet derivative.

Induction on the differentiability order applies the same criterion to each
fixed-direction derivative. The finite-dimensional characterization of
`ContDiffOn` in terms of evaluations of the Fréchet derivative then gives
`C^∞` on `U`. Composing with the chart gives the desired smoothness near
each original manifold point.
