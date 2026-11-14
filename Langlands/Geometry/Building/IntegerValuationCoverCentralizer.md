# Integer-valued centralizer compatibility under derived covers

This internal support module adapts the Library proofs in
`CentralIsogenyCentralizer` and `DerivedCentralizer` to an explicit
integer-valued valuation on any field. It reuses their actual algebraic
centralizer maps and root-function-family pullbacks. No new geometric
statement or local-field instance is assumed.

The proof first establishes naturality of the negative character-valuation
translation in every commuting torus-centralizer square, by evaluating on
rational characters and using injectivity of restriction evaluation. It then
substitutes this equality into the original V6 identity for the pulled-back
root functions. Equipollence-class compatibility follows pointwise from the
family identity. Both derived inclusions and central isogenies are covered.
All split torus, isogeny, derived subgroup and central complement hypotheses
remain explicit. The result constructs no building or compatibility class.
