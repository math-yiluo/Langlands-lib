# Compact averages of linear pullbacks of Schwartz functions

`SchwartzCompactAverage.average` gives the Schwartz function
\[
  x\longmapsto\int_Y w(y)\,\Phi(A_y x)\,d\mu(y).
\]
Here \(Y\) is compact, \(\mu\) is a finite Borel measure, the complex
weight \(w\) is continuous, and \(A_y\) is a continuous family of bounded
real-linear maps with a uniform bound \(\|x\|\le H\|A_y x\|\) for a
nonnegative \(H\).

The proof expresses each iterated derivative of a linear pullback as
the original derivative composed with \(A_y\) in every argument.
Joint continuity of this composition gives measurability. The bounded
weight and bounded family of operators give an integrable bound for
each derivative with respect to the finite measure. Differentiation
under the integral, followed by induction on the order, identifies
the iterated derivatives of the average with the corresponding
integrals of multilinear maps.

The lower norm bound transfers each power of \(\|x\|\) to a power of
\(\|A_y x\|\) in the Schwartz seminorm estimate. Integrating the
resulting uniform bound proves rapid decay of every derivative.

This is the compact averaging step before off-diagonal integration in
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §7.1, p. 44.

`iteratedFDeriv_average` exposes the derivative formula.
`continuous_average_weight` bounds each Schwartz seminorm of a
difference of averages by a fixed constant times the uniform norm of
the weight difference. For a compactly supported Schwartz function, the
pullbacks and their derivatives vanish outside a common compact ball.
Joint continuity on this ball makes their weighted derivatives
uniformly close to those of the original function when the linear map
is close to the identity in the parameter space. A continuous
nonnegative weight supported in that neighborhood has positive integral
when it is one at the parameter for the identity and the measure is
positive on nonempty open sets. Normalizing the weight gives the
required averages. Continuity in the weight then permits use of any
dense subset of the continuous weights.

`continuous_pullbackDerivative` gives joint continuity of the spatial derivatives in the linear pullback and evaluation point.
