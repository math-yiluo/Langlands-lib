# Transports from special blocks to full supercuspidal induction

This is a derived auxiliary construction for the associated-pair induction
argument. It uses the Library's actual normalized induction and constituent
relations. It does not establish the classification, the vanishing of any
exponent, or the assertion that every segment has length one.

`Langlands.Classification.segmentFactorZeroIso`, reused from
`TwoSupercuspidalAdjacentReducibilityProof`, removes an exponent-zero determinant twist by the
proved identity for real power twists. `twistedProductInducedZeroIso` applies
these actual block isomorphisms through the normalized product induction
functor. Its input is pointwise vanishing of the supplied exponents; its
conclusion is an isomorphism of the full induced objects with the same
ordered blocks.

`IsSegmentQuotient.exists_equiv_castRank_of_length_one` starts with the actual
surjective quotient map in `IsSegmentQuotient`. For a one-term segment,
`singletonSegmentInducedEquiv` identifies its induced source with the base
supercuspidal representation after exact rank transport. Composing the
quotient map with this identification yields a surjective intertwiner from
an irreducible source. It cannot be zero because the quotient is nontrivial.
Schur's lemma makes it injective, giving an actual representation equivalence.
`IsSegmentQuotient.supercuspidal_of_length_one` then transports admissibility
and all the actual Jacquet-quotient vanishings along that equivalence. The
supplied quotient's carrier and action are retained.

The field and block-carrier universes are independent. Normalized induction
has its existing `max uF uV` carrier universe. These constructions perform no
universe lowering.

The provenance is internal and derived: the results follow from the
published definitions and the one-block normalized-induction construction.
They supply elementary transports needed after the numerical block-rigidity
argument in Henniart's Appendix A, without claiming any of its analytic
or classification inputs.
