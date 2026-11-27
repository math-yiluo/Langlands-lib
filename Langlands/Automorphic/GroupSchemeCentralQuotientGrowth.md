# Growth from the fixed infinitesimal central ideal

Fix an affine connected reductive group over a number field, a smooth
archimedean realization with its differential commutator law, a positive-rank
closed matrix representation defining the adelic height, and a cofinite
ideal of the actual archimedean enveloping center. The functions are
rational-invariant adelic functions with plot-smooth archimedean slices.
Each function is fixed by an open finite subgroup and is annihilated by the
given ideal.

`CentralQuotientGrowthStatement` chooses finitely many central derivatives
and a height polynomial before choosing the function. A common bound for
these derivatives on the norm-one group bounds the function on the whole
adelic group by that bound times the height polynomial.

Lift a basis of the finite-dimensional center quotient to actual central elements. At
each adelic point, their evaluated derivatives give a vector of scalar coordinates. On a
ray of the logarithmic split central factor, the derivative of this vector is given by
multiplication by the class of the real infinitesimal generator in the center quotient.
The original action and the quotient give this equation also for generalized central
characters. The operator depends real-linearly on the logarithmic parameter.

Grönwall's inequality bounds the vector at time one by its norm at time zero times the
exponential of the operator norm. Expressing the identity of the center quotient in the
fixed basis recovers the original function. Bounding the operator norm by a constant
times the parameter norm and applying the polynomial bound for its exponential gives
the uniform height exponent. The product decomposition starts the ray at a norm-one
point with the same finite component.

Borel–Jacquet, *Automorphic forms and automorphic representations* (1979),
§1.6(1), printed p. 191 (PDF p. 186), uses the positive split central factor
and the finite-codimensional annihilator of §1.3(c), printed p. 190 (PDF
p. 185). The diagonal positive-idele coordinates come from
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.2.1, printed pp. 18–20 (PDF pp. 1–3).
`AdelicCentralLogParameter` gives their height bound. Multiplication in
the finite center quotient and Grönwall's inequality give the claimed
estimate.
