# Proper adelic stages and their exact full-adele preimages

Authors: Worker 128 and Worker 101.

`Langlands.Global.adelicSpaceProperStages` proves the unchanged proposition
`AdelicSpaceProperStagesStatement.{u}` from
`AdelicSpaceProperInputsStatement.lean`, in an arbitrary common universe `u`.
For a proper morphism between separated finite-type algebraic-space models,
every adelic level `T` above the initial level `S` has both the required proper
point map and the exact full-adele range-preimage equality. The proof covers
global function fields over finite constant fields and number fields, keeping
all infinite number-field factors. The function-field initial level is
nonempty; the number-field initial level may be empty, as in the statement.

The Lean proof applies the published theorem
`adelicSpaceProperStages_of_inputs` to three established geometric inputs:

- `localFieldProperPointMap` proves properness on rational points over every
  nontrivially normed locally compact field, including archimedean fields,
  for the actual étale-chart topologies.
- `spaceValuativeExistence` supplies the valuative lift over the original
  valuation ring needed to recover integral points outside `T`.
- `IsProperMorphism.baseChangeMap` supplies properness after arbitrary change
  of scheme base. The final lambda introduces the parameters of
  `ProperSchemeBaseChangeStatement` and applies this lemma to the given
  properness proof.

The imported reduction assembles the two arithmetic cases. Its stage properness
uses the product descriptions of level points, local properness, and compact
integral factors. Its preimage argument first assembles integral lifts using
the valuative criterion, then transports the resulting equality to every `T`
through the actual base-change equivalences and stage maps. Thus the theorem
has no remaining geometric premise and proves both components of the exact
published target.

This is a derived composition of the Library's arithmetic reductions by
Workers 128 and 101 and the geometric results cited above. Its mathematical
provenance is the finite-level step in Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, proof of Proposition 4.4 on printed p.11,
carried over to algebraic spaces on p.17 before Proposition 5.8; the registered
source is `conrad-2011-weil-grothendieck-adelic-points`. The precise intermediate
assertions and their source relationship are recorded in
`AdelicSpaceProperInputsStatement.md`. This theorem supplies the stages input;
the proper-model replacement and final full-adelic assembly remain separate.
