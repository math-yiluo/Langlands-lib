# Relative cohomology computes continuous corestriction

Let \(\Omega/K\) be Galois and \(E/K\) a finite intermediate
field. An open normal subgroup \(N\) contained in the fixing
subgroup of \(E\) has a finite Galois fixed field \(M/K\) containing
\(E\). The canonical inclusion \(E\hookrightarrow M\) gives the
upper relative cohomology groups. The map
`intermediateFixedFieldUnitInflation` inflates their classes to
continuous cohomology of \(E\) with the actual units of \(\Omega\).

The continuous transfer formula on a finite normal quotient and
the finite relative transfer identification give the commutative
square for inflation and corestriction. Every class over \(E\)
is computed by such a stage. First represent it by a class at a
finite normal stage of the open fixing subgroup. Then refine to
an open normal subgroup of the ambient Galois group and apply
finite-stage inflation naturality.

This is the passage from finite relative corestriction to continuous
cohomology in Serre, *Local Fields* (1979), Chapter XI, §§1–2,
printed pp. 166–168. The Lean proof uses the existing transfer on
finite quotients and the actual Galois correspondence. The ambient
Galois field can be the separable closure in any characteristic.
