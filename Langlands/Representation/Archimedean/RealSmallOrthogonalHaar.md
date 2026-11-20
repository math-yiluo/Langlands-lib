# Probability Haar integration on the real orthogonal groups in ranks one and two

`RealSmallOrthogonalHaarStatement` gives integral formulas for continuous complex-valued
tests on the actual matrix orthogonal groups. On `O(1)` the integral for Haar probability
is the average of the identity and the negative sign. On `O(2)` it is the sum of the angle
integrals on rotations and rotations multiplied on the right by the first-coordinate
reflection, divided by `4π`.

In dimension one the orthogonal equation makes the unique matrix entry a sign. Translation
by the negative sign exchanges the two points. The sum of a test and its translate is constant,
and left invariance proves the average formula.

In dimension two the determinant is a sign. A determinant-one orthogonal matrix has equal
diagonal entries and opposite off-diagonal entries. Its first column is a unit complex
number, and its argument supplies the rotation angle. Multiplication by the reflection
changes the sign of the determinant, giving the other component. The rotation is the
Library's `blockRotation 2 0` in the matrix orthogonal group.

The Lean proof uses two angle integrals at each orthogonal element `k`, with arguments
`rotation θ * k` and `rotation θ * reflectTwo * k`. The rotation law and conjugation by the
reflection turn these into translates of the two angle integrands at the identity. Full-period
integrals are invariant under shifts, so their sum is constant in `k`. On the other hand,
Fubini and left Haar invariance give `2π` times the original Haar integral for each of the
two terms. These identities give the stated normalization for every Haar probability measure.

These internal compact-group integration formulas supply the sign and angle coordinates for the
within-block Haar measure in the regular Cartan trace calculation.
