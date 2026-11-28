# Presentation independence of the regularized cone integral

`RegularizedOrthantSumExtensionalityStatement` compares two finite sums of
polynomial exponentials with purely imaginary coroot coordinates. The finite
sets of labels may differ, and several labels may have the same coordinate
exponent. If every listed coordinate is nonzero and the sums agree pointwise
on the real coordinate space, the closed formulas for the regularized integral
agree at every translated vertex. This is a presentation independence property
of the regularization used in Delorme (2023), §7, equations (7.8)–(7.12).

For each real `t > 0`, add `t` to every exponent coordinate in both sums.
The translated polynomial Laplace identity computes the displaced terms as
convergent integrals on the same reflected translated orthant. The all-positive
orientation has sign one. Integrability of each term allows the sum inside the
integral. After reflection, each displaced sum is the original sum multiplied
by the common exponential with exponent `-t` times the sum of the spatial
coordinates. Pointwise equality therefore gives equality of the displaced
formulas. Each formula is continuous at zero shift because its denominators
there are nonzero. Uniqueness of the right limit gives the desired equality.

`UnitaryPairingExpansion.regularizedConeIntegral_eq_of_eval_eq` applies this
argument to the coroot coordinates of normalized pairings. Taking the real
part of the parameter pairing verifies that the coroot exponents of a unitary
parameter are purely imaginary. The same finite sum argument applies when the
coordinate index set is empty.
