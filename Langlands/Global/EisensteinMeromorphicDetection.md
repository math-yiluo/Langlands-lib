# Propagating injectivity of a finite Eisenstein family

`HasLocalHolomorphicNumerators` records local open windows on which a
linear family admits weakly holomorphic numerators with scalar
denominators. Its regular parameter set is open and dense in the given
domain. On each local regular set the scalar evaluations are quotients
of holomorphic functions with nonzero denominator.

For a fixed evaluation matrix its determinant has local denominator
given by the original denominator raised to the dimension. Continuity
extends the determinant identity from a local regular set to the
intersection of that window and the common regular locus. One injective
member supplies a nonzero evaluation determinant. If all regular
members on a nonempty open subset failed to be injective, the determinant
would vanish there and hence throughout the connected domain by
`eq_of_hasLocalDenominators`.

This is an internal implementation of the injectivity propagation in
Langlands, *On the notion of an automorphic representation* (1979),
Lemmas 7–9, printed pp. 206–207 (Corvallis Part I PDF pp. 201–202).
`continuedLinearCombination_hasLocalHolomorphicNumerators` derives
the hypotheses from the common normalization of open-subtype
continuation witnesses, using continuous evaluations in the growth space.
