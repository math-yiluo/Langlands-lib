# Norm pullback for rank-one Shintani lifts

The Library theorem `IsCyclicAlgebra.isGalois` identifies a cyclic field
extension as Galois using its fixed-field clause. The powers of the chosen generator exhaust the
automorphisms. The field norm formula then identifies the scalar
rank-one cyclic norm with the scalar matrix of the field norm.

For two character models of rank one, the Lean proof computes their
ordinary and twisted character values using the finite-dimensional
trace. The Shintani identity at the identity element gives the trace
of the intertwiner. Its value is the nonzero Shintani constant. For
any unit, the identity at its associated rank-one pair now gives the
norm pullback formula after cancellation.

This is the rank-one form of the central-character comparison in
Henniart and Lemaire (2011), II.2.9, Remarque (3), printed p. 70
(PDF p. 78), literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
The lemma uses the Library's pointwise `IsShintaniLift` hypothesis.
