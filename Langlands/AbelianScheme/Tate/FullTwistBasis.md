# Integral and adelic bases of the full Tate twist

For an algebraically closed field \(K\) of characteristic zero,
`fullIntegralBasis` is a linear equivalence from the profinite integers
to the full inverse limit of the actual roots of unity of \(K\).
The proof takes a basis of each prime-adic twist from `integralRankOne`
and combines them with `fullPrimeProductComparison` using
`TateAdelicRank.assemble` in rank one. `TateAdelicRank.fullScalarEquiv`
is the ring equivalence from profinite integers to the product of the
\(p\)-adic integers with canonical projections
`ProfiniteIntegerRing.toPadic`. Its bijectivity proof uses continuity
and agreement on the dense image of the integers.
`fullToPrime_smul` compares the scalar actions on the root limits
through precisely those projections.
`geometricFullIntegralBasis` transports the basis to the global sections
of the geometric point \(\operatorname{Spec} K\).

For a commutative ring \(R\) and a supplied profinite-integer basis of
its full integral twist, `finiteAdeleBasisOf` extends that basis to the
rational twist for the specified comparison with the finite adeles of
\(\mathbf Q\). The map sends a finite adele to its scalar action on the
rationalization of the integral generator. The simple-tensor formula
for this action identifies the map with extension of scalars of the
integral equivalence. `finiteAdeleBasisOf_integral` identifies its value
on each integral scalar with the rationalization of the original
basis value. These are derived comparisons of the Library's actual
roots-of-unity limits and its residue and adelic scalar actions.
