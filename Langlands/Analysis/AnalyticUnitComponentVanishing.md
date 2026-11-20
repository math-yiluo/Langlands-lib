# Analytic componentwise vanishing for differential-stable families

Let \(A\) be a real Banach algebra and let \(f_v\) be a family of
complex-valued functions on \(A\), analytic at every unit. Suppose that for
each \(X \in A\) differentiation in the direction \(gX\) at units gives
another member \(f_{D(X,v)}\) of the family. The proposition
`AnalyticUnitComponentVanishingStatement` asserts that if every member
vanishes at the same unit \(p\), then each one vanishes on the connected
component of \(p\) in the unit group.

The proof fixes \(X\) and restricts the family to \(p\exp(tX)\). The derivative
of the restricted function is the restriction indexed by \(D(X,v)\). This
identity makes every derivative at \(t=0\) vanish by induction. Real analytic
uniqueness gives vanishing on the entire real line for each \(X\). The
exponential has identity strict derivative at zero, so the inverse function
theorem puts a neighborhood of \(1\) in its image. Left multiplication by
\(p\) yields vanishing near \(p\). The image in \(A\) of the connected
component of \(p\) is preconnected and consists of points of analyticity.
Analytic uniqueness on this image gives the assertion.

This internal result supplies a componentwise criterion for matrix
coefficients restricted to one real or complex factor of an archimedean
product. The exponential argument uses only the directions of that factor.
