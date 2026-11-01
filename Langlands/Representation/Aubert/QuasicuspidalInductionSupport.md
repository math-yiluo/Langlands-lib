# Support preservation for quasicuspidal induction

Author: Worker 165.

This internal derivation proves support preservation for the actual exact
finite-length Grothendieck group in positive rank. It makes no effectivity
claim for the alternating operator.

For an actual finite-length Levi-quasicuspidal representation `A`, let `v`
be the composition-factor vector of its actual normalized induction from
the block shape `B`. `QuasicuspidalInductionSupportStatement` says that
for every irreducible label in `v`, both each individual operator
`i_C r_C` and the unadjusted Aubert operator have factor vectors supported
in `v`. The conclusion concerns virtual factor vectors; cancellation
within the alternating sum is allowed.

`inductionJacquet_onIrreducibles_effective` proves positivity of every
individual term on every actual irreducible label, without a
quasicuspidality or support hypothesis. Realizing a basis generator gives
the actual irreducible representation's exact class. The canonical
Jacquet and induction class formulas then identify the image with the
class of an actual finite-length representation, whose composition
multiplicities are nonnegative.

`quasicuspidalInductionSupport` applies the actual scalar-term formula
`quasicuspidalInductionTerms`: each `i_C r_C` sends the entire induction
class to a natural-number multiple of itself. Transport to irreducible
coefficients uses the published inverse relationship between
composition-factor counting and realization of exact classes. The
positive integral-lattice support lemma forces each constituent column
to stay in the induction's support. Finally, outside that support every
column is zero, so every coefficient of their finite signed alternating
sum is zero there as well.

The substantial inputs are the actual finite-length preservation and
exact class formulas for normalized induction and Jacquet modules, the
exact finite-length comparison with the irreducible lattice, the
geometric-lemma scalar-term identity, and elementary positive
integral-lattice support control. No classification or irreducible-image
result is used. Every original short exact sequence relation, including
nonsplit sequences, remains in the Grothendieck quotient. The supplied
prime, p-adic field and topology are arbitrary; field and carrier
universes remain independent, with saturated carriers.
