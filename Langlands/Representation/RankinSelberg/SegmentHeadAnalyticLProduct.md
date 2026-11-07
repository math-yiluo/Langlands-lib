# Actual shifted analytic L-products for supplied segment heads

Author: Worker 1765.

This internal adapter keeps the supplied segment heads and actual base actions.
The segment-head L-factor formula is an explicit premise. It does not prove
that formula or the associated-pair induction theorem.

`IsPadicShiftedReciprocalProduct` is the proposition that a supplied polynomial's
spectral reciprocal equals a finite product of supplied polynomial reciprocals
at supplied real translates, at every complex input. It retains the actual
residue cardinality. It imposes no certificate or nonvanishing conditions by
itself; these are explicit hypotheses of the theorem constructing it.

`realTwistPolynomial_eval_spectral` identifies evaluation of the published real
polynomial substitution with translation of the complex spectral variable.
It uses the positive actual residue cardinality and `spectralPoint_add`.

`IsPadicRankLPolynomial.reciprocal_eq_of_realTwists` applies the published
certificate transport in both variables and polynomial uniqueness. Every
polynomial certified for the actually twisted actions has the translated
reciprocal of the original certificate. Ranks are arbitrary, with independent
carrier universes; a certificate itself excludes zero rank.

`reciprocal_of_segmentHeads_realTwists` constructs this proposition from the explicitly supplied
segment-head product formula. It converts its polynomial product into a
product of inverses by evaluation, then identifies each factor using the base
certificate and the preceding twist lemma. For the zero-based index j, the
real shift is len(Delta) + len(Delta') - 2 - j + s + t. All functions are
ordinary complex functions with totalized inverse, so the equalities also
hold at denominator zeros. Pole information must still be obtained from
meromorphic orders.

The topology is the canonical topology of the supplied p-adic field. The
character and self-dual Haar measure are retained throughout. All results
are derived from the imported Library; no new literature assertion is made.
