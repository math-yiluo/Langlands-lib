# Assembly of the direct-limit equivalences

Worker 606, with the fibre-locus comparisons of Worker 634.

This internal derived unit assembles the direct-limit equivalences from
`DirectLimitGeometry` and `FibreLocusComparisons`. It proves whole-group
reductivity descent without further hypotheses. Its two semisimple descent
lemmas explicitly assume that the initial semisimple identity-component locus
is open. The final theorem proves the implication
`IdentityComponentSemisimpleLocusOpenStatement →
DirectLimitReductiveStatement`; it does not prove the openness premise.

`directedEventually` is exactly the eventual-stage predicate of the target:
there is an index above the initial index such that the dependent predicate
holds at every later index. Pointwise equivalent predicates have equivalent
eventuality. Eventuality commutes with conjunction because directedness supplies
a common upper bound for the two witness indices.

The reductivity comparison expresses `IsReductive` as geometric connectedness
and fullness of the reductive identity-component locus. Each condition has the
direct-limit equivalence supplied by `DirectLimitGeometry`. The conjunction
lemma combines their two eventual witness stages, and the same fibre-locus
comparison at each stage gives eventual reductivity.

For the semisimple identity-component locus, arbitrary base change is the exact
preimage equality proved in `FibreLocusComparisons`. The open-locus detector of
`DirectLimitLocus` therefore gives eventual fullness under the explicit
openness premise. Relative semisimplicity is geometric connectedness and
fullness of this semisimple locus. The same conjunction argument proves its
descent. Fullness of the semisimple locus is definitionally the condition on
every geometric fibre's identity component used in the target's third clause.

The final theorem introduces every parameter of the unchanged target, obtains
openness from its explicit premise, and assembles these four equivalences.
All indices, rings and schemes remain in the arbitrary universe `u`, with no
restriction on ring maps and no Noetherian or nontriviality assumption. This
is a derivation from the cited Library interfaces; it introduces no additional
literature assertion. The exact unconditional proof still requires a separately
proved and published semisimple-openness statement.
