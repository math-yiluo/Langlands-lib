# Convergence of reflected ordinary integrals for genuine smooth real pairs

`RealPairedUnequalDualConvergenceStatement` gives a common right half-plane
of absolute convergence and holomorphy for the reflected rectangular
integrals on genuine smooth vectors of a completed Banach projective pair,
with the larger rank in the first slot. The continuous scalar form has
opposite nonzero Whittaker scales in the independent slots. The first slot
uses the reflected rectangular argument and the tail Weyl multiplier, and
the second uses the reflected comparison argument. The rectangle carries
the self-dual measure of the given additive scale. For a form with the
pure tensor evaluation rule, the kernel on a pure smooth tensor equals
the ordinary scalar `realUnequalDualKernel`.

The reflected unipotent covariance follows by the Weyl inverse transpose
identity and commutation of the two slot embeddings. At a rectangular
point, left multiplication in the common group is left multiplication
by the padded unipotent in the first slot and by the original unipotent
in the second. The additive characters cancel. This gives the quotient
invariance needed for convergence.

For the bound, use invariance of the norm under upper unipotents in the
first slot to pass to its Iwasawa torus. The tail Weyl multiplier is
orthogonal, and reverse negation of the logarithmic coordinates preserves
both the simple-root sum and the absolute-coordinate sum. The paired gauge
therefore bounds the reflected coefficient by arbitrary simple-root decay
and a fixed power of the second slot's height. The rectangular exponent
comparison converts the first bound to joint decay in the positive toral
coordinates and the rectangle, while the reflected toral height estimate
controls the second slot. The scalar rectangular convergence criterion
then gives the desired half-plane. The pure kernel identity uses the
coordinate formulas for the representation on pure smooth tensors.

At equal ranks, `RealPairedEqualDualConvergenceStatement` uses the two
reflected arguments on the common group with no tail Weyl multiplier.
The Fourier transform of the supplied Schwartz test provides the decay
in the positive last logarithmic coordinate. The toral estimate of the
reflected pair controls the remaining simple-root coordinates. The
common scalar toral convergence theorem gives an abscissa independent
of the smooth vector and Schwartz test. The pure tensor evaluation
rule identifies this kernel with the usual equal-rank scalar dual
kernel using that Fourier transform.

This combines the reflected kernel of Theorem 2.1(iii), p. 6, with the
equal-rank and rectangular convergence arguments of §5.1–5.2, pp. 32–35,
for the tensor product setting of §12.3, pp. 89–90.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=33).

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
