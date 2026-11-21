# Comparing the actual group-Levi packet with ambient coefficients

This auxiliary comparison makes explicit the identification of the
full-group coefficient map used in the proof of Waldspurger VIII.4.2,
printed p. 330, PDF p. 96. It uses the ordinary coefficient map described
in V.1, printed p. 288, PDF p. 54. The split component, quotient Haar measure
and representation carrier universe are those of the ambient discrete series.

The Levi indexed by every simple root is the literal full subgroup of the
rational points. `rationalFullLeviOrbitHomeomorph_val` identifies the class at a
transported orbit point with the pullback of the ambient class. The square
integrability comparison uses the transported split component and quotient
Haar measure.

`rationalFullLeviAmbientOrbitCoefficient` evaluates the section's actual
coefficient at the corresponding Levi orbit point. Choose any inducing
representative of that point. The full-Levi product tensor equivalence
identifies its section value with an ordinary coefficient tensor for the
ambient pullback of this representative, preserving the compact-probability
coefficient map. Equality of smooth-dual classes gives an equivariant
linear equivalence with the pullback of the canonical ambient representative.
The composite of the two group maps is the identity on the ambient group,
so the resulting tensor transport preserves the coefficient as a locally
constant function.

`rationalFullLeviOrbitCoefficientTensor` chooses this ambient tensor at
each point, with carrier in the original universe `uV`. Its coefficient
is the transported section coefficient. The comparison supplies a
pointwise identity for the orbit integral in VIII.4.2.
