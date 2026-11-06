# Contragredient twist parameters give denominator roots

This internal derived unit proves the converse direction needed for the
equal-rank supercuspidal L-factor calculation. The field and the two
representation carriers have independent universes. The topology is the
canonical topology of the supplied p-adic field.

`HasNormalizedContragredientTwistRoots` says that each actual equivalence
from the normalized determinant twist of the first representation at `-u`
to the smooth contragredient of the second forces the polynomial to vanish
at the spectral point `q^u`.

The proof assumes the full supercuspidal Kirillov statement, an irreducible
supercuspidal first representation with a nonzero standard functional, an
irreducible second representation of inverse Whittaker type with a nonzero
fixed functional, a compatible quotient measure, the analytic conclusion
for those fixed functionals, and their normalized denominator polynomial.
The Kirillov input remains explicit. No analytic statement or compatibility
existence is asserted in this module.

The proof chooses the compact central row shell and a coefficient pair
whose integral converges and has positive real part at `-u`. Multiplicity
one moves the second functional to the prescribed functional by scaling
the second vector. Compact support identifies the shell's rational
continuation with this positive integral, including denominator regularity.

If the normalized polynomial did not vanish at the spectral point, its
denominator-clearing property would make the original row-test
continuation regular there. Schur's central characters give nonzero
scalar actions at the inverse-uniformizer central element. The supplied
twisted contragredient equivalence forces the product of these scalars
to be the spectral point to the common rank. The actual central
translation identity therefore forces the shell continuation to
evaluate to zero. Both rational products are evaluated with explicit
regularity guards. This contradicts the positive integral.

The regularity helper follows by expressing a continuation as the product
of a Laurent polynomial and the inverse of the normalized polynomial.
The result supplies only twist-to-root; it does not assert the converse,
separability, or the finite product L-factor formula.
