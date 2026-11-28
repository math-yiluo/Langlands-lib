# Uniform ordinary polarization degree for normalized Harris objects

Let \(X\) be an actual polarized Harris action and let \(\mu\) be a
primitive representative of its polarization ray in the sense of
`HarrisPrimitivePolarization`. A positive integer multiple of \(\mu\)
is the supplied polarization of \(X\).
`primitivePolarization_four_isPolarization` applies
`polarizationDoublingDivision` twice to obtain a polarization
\(4\mu\) on the same abelian scheme with the same dual.

On a connected locally noetherian base, at a supplied algebraically
closed point of characteristic zero,
`harrisPrimitiveOrdinaryDegreeIndex` is the positive degree index
given by `DualWitness.doubledDegreeIndex` for the polarization
\(2\mu\). Its square is the constant native rank of \(4\mu\).
If all positive integers are units on the bases and the finite
étale torsion input holds, `primitivePolarization_nativeRank_eq`
compares this rank across any two objects with normalized frames.
Equality of squares of natural numbers then gives
`harrisPrimitiveOrdinaryDegreeIndex_eq`, so the index is independent
of both the object and the indicated geometric point.

`harrisQuadrupledPrimitive_eq_of_squareDegree` identifies the original
polarization with \(4\mu\) when the two maps have the same positive
square degree in positive relative dimension. If the polarization is
\(k\mu\), the proof compares the ranks of \(4(k\mu)\) and \(k(4\mu)\)
on a geometric fibre. Multiplication on a dimension \(g\) abelian
variety contributes rank \(r^{2g}\) for multiplication by \(r\).
Cancelling the common positive degree and using \(g>0\) gives \(k=4\).

`HarrisPrimitiveOrdinaryDegreeUniform` expresses that one degree index
works on all such normalized objects for the fixed Harris and Weil
data. `exists_harrisPrimitiveOrdinaryDegreeUniform` gives a positive
index satisfying that predicate. If index \(1\) satisfies it, use
that index. Otherwise its failure supplies a normalized object, whose
positive index works for every other such object by the rank comparison.
These conclusions derive from the Library's primitive polarization,
square-degree and normalized finite kernel comparisons.
