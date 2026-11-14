# The derivative root datum of a descended unramified facet model

`unramifiedFacetRootDatum` proves the existing Library proposition
`UnramifiedFacetRootDatumStatement` at arbitrary universe `u`, with that exact
proposition as its type. All seven building hypotheses, all eight
apartment-descent hypotheses, universal quantifiers, model-characterization
hypotheses, and supplied torus, quotient and reflection data remain those of
the unchanged statement.

The implemented proof applies the published
`unramifiedFacetRootDatum_of_integralOppositeFactors` to the unconditional
`integralOppositeFactors` proved in the accompanying `IntegralOppositeFactorsProof`
module. Its paired Markdown describes the necessity and sufficiency arguments
for the actual integral-point and radical-preimage subgroups.

The reduction uses this opposite-factor criterion to compare the actual roots
of the supplied reductive quotient with the apartment facet's derivative roots
under the canonical character specialization through the supplied integral
torus. The published root-datum assembly then identifies the quotient's actual
root-coroot graph with `apartmentDerivativeRootCorootGraph`, proving the complete
`HasApartmentDerivativeRootDatum` predicate for every datum quantified by the
statement. The construction retains the actual quotient and its torus, rather
than choosing an unrelated abstract root system.

This is an internal composition of the imported proofs. The statement's Lean
and Markdown pair and the pairs in its import closure are unchanged.
