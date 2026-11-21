# The cyclic norm conductor formula from p-adic data on the base

For a cyclic extension of local fields, a p-adic presentation of the
base field supplies the arithmetic identity for the norm pullback of
a continuous quasicharacter. The upper field has the given local-field
structure and the given relative module topology. The conclusion is
the sum of actual principal-unit conductors with the specified
residue degree and trace-defined different exponent.

The Lean proof uses the continuous relative algebra map to construct
compatible p-adic data on the original upper carrier. The cyclic
algebra certificate supplies finiteness and a cyclic Galois group.
The two supplied p-adic structures thus satisfy the hypotheses of
`padicNormPullbackConductor`. A pointwise identification of the
continuous norm pullback with its stated character gives the result.

The relative topology is the one in Serre, *Local Fields* (1979),
Chapter II, §2, Proposition 3. The conductor comparison supplies the
rank-one arithmetic used in equation (6.7) of Arthur–Clozel (1989),
Chapter 1, printed p. 60.
