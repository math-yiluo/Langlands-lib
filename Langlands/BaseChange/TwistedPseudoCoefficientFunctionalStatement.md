# A spectral functional with the prescribed pseudo-coefficient values

`TwistedPseudoCoefficientFunctionalExistenceStatement` isolates the spectral
construction before test-function realization in Henniart–Lemaire II.5.13,
printed pp. 113–114. For the data of the twisted pseudo-coefficient existence
statement in ranks at least two, it asks for a linear functional on
`Distribution (GL_n(E))`.

The functional must be compactly dominated and regular on the induced families
in `IsSigmaInducedRegularFunctional`. It must take the value one on the
actual twisted distribution of the given pair and zero on all its inequivalent
irreducible admissible tempered competitors with the same central character.
These are the values required when a test function realizes the functional
on irreducible twisted characters. Both the functional conditions and the
character evaluations use the given Haar measure. The formulation uses the
complex dual of the existing distribution space.
