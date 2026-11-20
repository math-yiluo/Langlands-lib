# Partial Fourier transforms of Schwartz functions on a real product

`SchwartzPartialFourier.transform` takes a Schwartz function
\(\Phi\) on \(E\times F\), with \(E,F\) finite-dimensional real inner
product spaces, to its Fourier transform in the second variable.
`transform_apply` identifies the value at \((x,\xi)\) with the usual
Fourier transform of \(y\mapsto\Phi(x,y)\) at \(\xi\).

For the first coordinate, the proof differentiates the partial integral
under the integral sign. Each parameter derivative is bounded by a sum
of derivatives of the original test times powers of the integrated
variable. Arbitrarily high Schwartz decay absorbs these powers, gives
an integrable bound, and also allows any power of the first coordinate
in the resulting derivative estimate.

Fubini identifies the Fourier transform in the first coordinate of the
partial integral with a slice of the full Fourier transform. The volume
of the Euclidean product agrees with the product of the individual
volumes. The first-coordinate function is continuous and integrable,
and the slice of the full transform is Schwartz. Fourier inversion thus
gives a second expression for the partial integral using the same
construction with the full transformed test, exchanged coordinates,
and a reflected frequency. Its first-coordinate estimates control the
second coordinate of the original integral. The two bounds give
Schwartz decay in the product norm.

This supplies the real inner product space operation behind the
partial transform in Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), §7.2, p. 48. The complex trace pairing is obtained from the
real pairing by a linear change of the frequency.
