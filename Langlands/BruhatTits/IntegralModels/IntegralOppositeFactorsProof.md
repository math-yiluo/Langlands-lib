# Integral opposite factors and the actual radical preimage

`integralOppositeFactors` proves the existing
`IntegralOppositeFactorsStatement` at arbitrary universe `u`. It retains every
supplied smooth connected model, closed split integral torus with maximal split
generic fibre, actual reductive quotient, root, nonidentity integral root point,
and prescribed normalizing opposite-factor pair in that statement.

The necessity direction is
`IntegralTorusData.not_mem_positivePoints_of_integral_oppositeFactors`.
For sufficiency, choose an integral section representing the given root point.
The fppf quotient's equality of its full scheme kernel with the actual radical
image identifies trivial quotient reduction with radical reduction. Thus the
hypothesis excluding the positive subgroup makes this section's quotient
reduction nonidentity.

The integer ring of the local field is Henselian. Generic maximality of the
supplied torus transports through its specified generic isomorphism. The
Henselian split-rank theorem then gives maximality of its residue torus, and
passage through the unipotent radical quotient over the perfect residue field
gives maximality of that same torus in the quotient. Smoothness of the projection
and smooth connected unipotence of its full scheme kernel follow from the
supplied reductive-quotient predicate.

The proof lifts the actual generic character through the split integral torus.
`IntegralTorusGenericRoots` transports both root membership and the complete
opposite-pair predicate while preserving the given generic point and ordered
pair. A positively pairing generic cocharacter lifts through that same integral
torus. Compatibility of the canonical special pairing and base-change
invariance prove positive pairing over the integer ring.

Finally the published relative-root-system theorem applies to the transported
maximal split generic torus.
`IntegralModel.integral_oppositeFactors_of_residueQuotient` now applies to the
original integral section and prescribed ordered pair, proving both factors
integral. This is internal composition of the imported results; it introduces
no quotient, component-action, root-lift or reflection premise into the existing
statement.
