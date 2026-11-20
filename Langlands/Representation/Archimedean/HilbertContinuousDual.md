# The continuous Hilbert dual and transpose kernel traces

The continuous complex-linear dual carries its operator norm. Its Hilbert
inner product uses the Riesz map \(e:H\to H'\) by
\(\langle L,M\rangle_{H'}=\langle e^{-1}M,e^{-1}L\rangle_H\). Thus \(e\)
is conjugate-linear isometric and conjugates the original Hilbert inner
product. This Hilbert structure is provided as a scoped instance.

For a jointly continuous Hilbert action of real or complex
\(\mathrm{GL}_n\), `inverseTransposeContinuousDual` acts on continuous
functionals by inverse precomposition after the inverse-transpose twist.
This action is jointly continuous. Given a continuous compactly supported
kernel \(\kappa\) and a Borel Haar measure, Riesz transports the inverse-adjoint
inverse-transpose average with kernel \(\overline{\kappa}\) to the actual
dual average with kernel \(\kappa\). The scalar conjugation follows from
passing the conjugate-linear Riesz map through the Bochner integral.

For a regular Haar measure, the average of the inverse-adjoint twist
against \(\overline{\kappa}\) is the adjoint of the original average
against \(\kappa\) composed with ordinary transpose. When that original
average is trace class, so is the continuous dual average. The adjoint
and Riesz transport each conjugate the operator trace, so the dual
average has the original trace on the ordinary-transposed kernel.

This internal covariance identity combines Haar transpose change of
variables with Hilbert basis trace transport.
