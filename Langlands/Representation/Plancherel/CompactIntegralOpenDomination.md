# Local domination on open regions of full convergence

`transportedRationalUnramifiedCharacterCoordinates` composes character transport through a multiplicative homeomorphism with the canonical complex coordinates of the actual rational points. Its evaluation lemma expresses each transported character value as the Laurent monomial given by the valuation of the original point.

`compactIntegralLocallyDominatedOn_of_isOpen_of_monomials` uses these monomials to produce the local domination required for compact standard intertwining integrals. Around a point of an open region, choose finitely many characters by multiplying the coordinate radii by small positive or negative exponential factors. Openness puts all those characters in the region. For each Laurent monomial, the signs of its exponents select a corner of the box that bounds its absolute value throughout a neighborhood. The compact extension at each point is a fixed vector times one character value, so the sum of the scalar integrand norms at the corners dominates the scalar integrand. Full convergence makes each summand integrable for the same quotient measure.

This is a derived analytic implication for a supplied open region of full convergence. Both openness and full convergence of the region are explicit premises.
