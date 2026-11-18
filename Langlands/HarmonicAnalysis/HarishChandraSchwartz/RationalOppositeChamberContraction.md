# Inversion of actual chambers and opposite contraction

This derived supporting unit for Waldspurger II.3.3 and the VIII.3.1
tail cutoff proves that inversion sends the full actual minimal
chamber to its opposite. Its source is the exchange of `P₀` with its
opposite at the start of the proof of Lemma II.3.3, printed p.256,
and its use for the inverse-conjugation estimate on the opposite
radical in Proposition VIII.3.1, printed p.325. The original is
registered as `waldspurger-2003-plancherel`,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).

`IsGenericCocharacter.neg` uses bilinearity of the lattice
pairing to preserve nonvanishing under negation. With negation-stability
of the actual relative roots,
`mem_positiveRelativeRoots_neg_iff` identifies opposite positive roots
with negatives of original positive roots.
`mem_simpleRelativeRoots_neg_iff` also transports the condition that a
positive root is not a sum of two positive roots. This uses the exact
indecomposable-positive-root definition and retains nonreduced root
systems.

`inv_mem_rationalMinimalChamber_neg` obtains root negation-stability
from the proved actual relative root system of a connected reductive
group and maximal split torus. Negating the root and inverting the
torus parameter produce the same integer character order. Thus the
original chamber inequalities give the opposite chamber inequalities
on the inverse actual point, with no section restriction.

The previously proved actual minimal-parabolic contraction estimate
applied to the opposite generic cocharacter then controls
`1 + rationalHeight ρ (a⁻¹ * p * a)` uniformly by a positive multiple of
`1 + rationalHeight ρ p`, for `a` in the original full chamber and `p`
in the opposite minimal standard parabolic.

The precise supporting theorem is
`exists_one_add_rationalHeight_inv_conj_le_on_opposite`. The closed
Prop-valued summary
`RationalOppositeChamberConjugationHeightStatement` specializes the
finite index to nonempty `Fin N`; its proof is
`rationalOppositeChamberConjugationHeight`. The supporting theorem
allows every nonempty finite matrix index type.

The field universe and characteristic are arbitrary, and no closedness
of the finite nonempty matrix realization, compact adaptation, Cartan
or Iwasawa decomposition is assumed.
This unit gives the opposite contraction bound. It does not yet prove
the maximal-parabolic open-cell estimate or the outside-truncation
tail cutoff.
