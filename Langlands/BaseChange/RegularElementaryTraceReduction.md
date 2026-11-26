# The fixed level and double-coset trace of a regular elementary test

`RegularElementaryTraceReductionStatement.{u,v}` gives a common principal
congruence level and a trace identity for the Library's regular elementary
tests on `GL_(r+1)(E)`. The field and representation carrier universes are
independent. The trace identity uses any Haar measure and any intertwining
equivalence for the chosen entrywise automorphism.

A regular elementary test is a finite sum over cosets of the subgroup
with diagonal reduction in the spherical subgroup. The summands are
pullbacks of one double-coset indicator under twisted conjugation.
The spherical subgroup normalizes the first principal congruence
subgroup, and the field automorphism preserves the spherical subgroup.
The smaller double-coset indicator is invariant on both sides by the
first principal congruence subgroup, so every pullback is too. The
resulting fixed level is independent of the strictly decreasing weight.
`regularElementaryBaseChangeTests_mem_firstCongruence_biInvariant` applies
this to both members of the pair, with the scaled weight on the base side.

For the trace, a pullback by twisted conjugation replaces the integrated
operator composed with the twist by a conjugate operator. The modular
factor from right translation is one on the compact spherical subgroup.
Finite-rank trace is conjugation invariant, giving the trace of the
double-coset indicator multiplied by the coset count.

These are intermediate steps for the regular-weight trace in
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), I.5.3, Proposition, printed pp. 31–32
(PDF pp. 39–40). The source argument uses the orbital chart Jacobian.
The proof here uses the finite coset decomposition and leaves the trace
on the diagonal-reduction double coset in terms of the original
representation.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
