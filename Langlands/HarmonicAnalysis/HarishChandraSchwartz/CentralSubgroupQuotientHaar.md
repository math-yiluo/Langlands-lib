# Haar invariance on the actual split-central quotient

This derived measure-theoretic unit supplies the quotient-measure invariance
used for the quotient-L² form in Waldspurger (2003), VIII.4. It generalizes
the Library's full-center quotient argument to any closed central subgroup,
then specializes to the actual split-component point image.

For an ambient inner automorphism, restriction to a central subgroup is the
identity. The published multiplicativity of automorphism Haar moduli across
a closed normal subgroup therefore identifies the ambient conjugation
modulus with the quotient's conjugation modulus. Ambient unimodularity
makes this value one, and the published conjugation criterion gives right
invariance of every regular Haar measure on the quotient.

A regular two-sided Haar measure is invariant under inversion: its inverse
is a scalar multiple of itself; applying inversion twice makes the square
of that positive scalar one, hence the scalar is one. The proof uses a
compact set of positive finite measure and changes no normalization.

On actual rational points, the split-component image is closed and central.
The published reductive unimodularity and standard-cocharacter proofs
supply ambient unimodularity. Second countability gives regularity of the
specified Borel quotient Haar measure. Thus
`rationalSplitCentralQuotientHaar_invariant` proves both right and inversion
invariance for every Haar measure appearing in the VIII.4.2 targets, with
no additional analytic assumption or change of that measure.

Inversion invariance reuses the existing generic theorem `Langlands.isInvInvariant_of_isMulRightInvariant` from `Langlands.Group.GL.LeviCentralQuotientMeasure`.
