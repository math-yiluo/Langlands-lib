# Actual reflections from a supplied root-sign Coxeter system

This internal module pulls an arbitrary supplied Coxeter system on the actual
scheme relative Weyl quotient back to the finite root pairing witnessing
`HasRelativeRootSystem`. It uses the faithful-image group equivalence and the
bijection between the functional base and the literal simple characters.
The pullback preserves length and the right root-sign criterion.

If the torus is split and the cocharacter is generic, its evaluation functional
is nonzero on every witness root. `RootPairingCoxeterUniqueness` therefore
identifies every supplied simple generator with the actual witness reflection.
Transport gives `IsRelativeReflection` for every supplied simple generator.
No integral-coroot realization is assumed. Nonreduced roots, arbitrary fields
and the original simple-character labels are retained.
