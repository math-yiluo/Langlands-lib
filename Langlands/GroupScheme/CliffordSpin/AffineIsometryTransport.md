# Isometric coordinate transport for affine Clifford lifts

`Langlands.GroupScheme.CliffordSpin.CliffordSpinAffineIsometryTransportStatement`
identifies the affine Clifford lift schemes of two quadratic spaces by an
isometry carrying the chosen basis of the first space to that of the second.
It applies over a field in which two is invertible and describes the map
on points over every commutative coefficient algebra.

The coordinate homomorphism changes the Clifford unit by the tensor
extension of `CliffordAlgebra.equivOfIsometry`. It retains the action matrix
because the bases correspond entry by entry. The Clifford algebra map
commutes with grading and reversion and sends each generator to the
matching vector generator. Thus it preserves the defining coefficient
equations. Corepresentability gives the scheme map, and applying the
construction to the inverse isometry provides its inverse.

This internal comparison lets the Clifford block extension be expressed
in the scalar matrix coordinates used for the spin stabilizer in Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), §§5.9–5.10,
pp. 93–95.
