# Extensionality of finite Cartier points by evaluation

`schemeDualPairingOnRestrictions` takes a finite locally free commutative
group scheme `G` over `Spec R`, represented by finite, flat and locally
finitely presented structure morphism assumptions. It sends a point of
the actual Cartier dual on a test scheme `T` to the evaluations of its
restrictions against all primal points on schemes over `T`.
`schemeDualPoint_ext_of_pairing` proves that these evaluations determine
the original dual point, giving injectivity of the assignment.

The equivalence with represented relative characters sends both points to
actual characters. Restriction commutes with that equivalence, and the
represented characters evaluate by the finite Cartier pairing. The result
then follows from extensionality for relative group-scheme homomorphisms.

This is a derived consequence of the Library's finite Cartier evaluation.
It supplies a way to compare dual maps on the split polarized product in
Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), before (6.17).
