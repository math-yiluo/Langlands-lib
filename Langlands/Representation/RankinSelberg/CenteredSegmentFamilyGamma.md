# Actual gamma germs and rigidity of centered segment families

This internal adapter composes the actual rational gamma formula, the two
centered L-product identities, and the proved Appendix pole-counting theorem.
All representation-theoretic factor identities and the real-axis gamma order
restriction remain explicit premises. It does not prove
`AssociatedSupercuspidalInductionStatement`.

`IsCenteredSegmentFamilyGammaGerm` records equality on a punctured neighborhood
of every complex point between the rational spectral value and the Appendix
`blockGamma` built from the supplied actual segment parameters, real exponents,
base functions and epsilon function. It makes no equality claim about the
values assigned at a displayed pole or a cancelled singularity.

The L-product-pair adapter first substitutes its two identities in
`polynomialGammaExpression`. The published
`rationalSpectralValue_eventuallyEq_polynomialGammaExpression` then gives the
punctured equality, using the actual residue reflection and a nonzero dual
polynomial. Thus orders agree even at polynomial zeros. The canonical epsilon
monomial is analytic and nonzero everywhere by the existing exponential and
integer-power lemmas, so it supplies the epsilon units required by Appendix
rigidity.

`segmentRigidity` transfers the explicitly supplied real-axis positive-order
restriction through the germ equality and applies the proved
`appendixBlockRigidity`. Its length parameter is the original segment length
minus one; positivity of segment lengths converts a zero parameter into a
one-term segment. The real exponents vanish as well.

The final theorem uses the actual centered bases of a supplied unitary generic
block datum. The existing Hermitian partner construction supplies the numerical
symmetry and all base-pair conditions. The two L-products, the exact rational
gamma formula, nonzero dual polynomial, and real positive-order restriction
remain assumptions. No local classification, arithmetic match, or global gamma
comparison is constructed here. The field topology and residue cardinality are
canonical, and the original smooth actions and chosen segment parameters are
retained.

The provenance is internal composition of the named Library constructions and
proofs. The pole argument used is the published attained-smallest-pole proof in
`AppendixPoleCountingProof`, including its reflection and noncancellation
inputs; this adapter does not use the disputed largest-positive-pole step of
the original appendix.
