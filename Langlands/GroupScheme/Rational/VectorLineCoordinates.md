# Weights and polynomial maps in actual vector-line coordinates

This internal derived module constructs scalar coordinates for actual vector
lines over arbitrary fields. It supplies a single-character coordinate system
for any action of a specified split torus, and the additive polynomial of an
actual homomorphism in supplied natural line coordinates.

For the character statement, the published torus-action linearization theorem
first makes the action linear. Homogeneous coordinates diagonalize it by actual
characters on every scheme test. Uniqueness of vector dimension shows that the
homogeneous system has one coordinate, hence one weight.

For the polynomial, take the source point over `k[X]` whose coordinate is `X`,
apply the actual group homomorphism, and take its target coordinate. Naturality
shows that evaluating this polynomial at any affine source coordinate recovers
the coordinate of the actual image. Multiplicativity of the group homomorphism
and additivity of vector coordinates imply additivity over every coefficient
algebra, including nonreduced ones.

Provenance: derived from the Library's actual torus-action linearization,
homogeneous coordinates, vector-dimension uniqueness and natural affine vector
coordinates. No separability, perfectness or infinitude is assumed. This module
does not assert that any character is a root or prove the isogeny comparison.
