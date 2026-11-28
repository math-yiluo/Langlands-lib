# Primitive factors of positive-dimensional polarizations

`DualWitness.primitivePolarizationFactor` supplies an actual primitive
homomorphism \(\mu\) to the chosen dual such that the given polarization
is a positive integer multiple of \(\mu\). Its inputs include a positive
relative dimension, invertibility of positive integers on the base and
an algebraically closed geometric point.

If \(k\mu=\lambda\), the \(k\)-torsion at the point injects into the
kernel of the polarization, by `Tate.levelMap_nsmul_self`. The
geometric torsion rank formula gives at least \(k\) torsion points
because the relative dimension is positive. The polarization kernel is
finite. This bounds the positive divisors of the polarization, so
`Tate.exists_isPrimitiveHom_nsmul_eq` gives a primitive factor by
maximizing the divisor.

`DualWitness.isPolarization_double_of_primitiveFactor` uses
`polarizationDoublingDivision` to recognize \(2\mu\) as a polarization.
On a connected locally noetherian base with invertible integers,
`DualWitness.double_primitiveFactor_transport` compares the factors
of two polarizations under an actual abelian-scheme isomorphism
satisfying an integral cross-multiple equation. It applies
`DualWitness.transportMap_eq_of_primitive` with the proved
polarization-ray positivity result, then uses additivity of dual
transport on the double. The result is an exact equality of actual
polarization maps.

These proofs use the torsion rank, primitive Hom and polarization-ray
constructions in their imports.
