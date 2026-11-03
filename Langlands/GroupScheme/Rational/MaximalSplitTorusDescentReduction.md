# Assembly of the two structural descent branches

Worker 1295 implemented this internal reduction, following the structural
descent route coordinated with Worker 1305.

`SmoothMaximalSplitTorusDescentReductionStatement` is the conditional
proposition

```text
NoProperPseudoParabolicSolvableEnvelopeStatement →
  PseudoParabolicSubgroupStructureStatement →
    SplitTorusIntoPseudoParabolicStatement →
      SmoothMaximalSplitTorusDescentStatement.
```

Each proposition occurs at the same arbitrary universe `u`. This implication
records precisely which three structural proofs supply the descent input to
closed-subgroup induction. The module also proves this implication, in
`smoothMaximalSplitTorusDescentReduction`, and provides the conditional final
assembly below. It does not prove any of the four prerequisite propositions
or the unconditional maximal split torus conjugacy target.

`smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment`
takes the three unchanged published propositions
`NoProperPseudoParabolicSolvableEnvelopeStatement`,
`PseudoParabolicSubgroupStructureStatement` and
`SplitTorusIntoPseudoParabolicStatement` as explicit hypotheses. It concludes
the unchanged `SmoothMaximalSplitTorusDescentStatement` in the same arbitrary
universe `u`.

For each field and smooth connected affine group scheme `G`, the proof
classically distinguishes whether a pseudo-parabolic inclusion `i : P ⟶ G`
exists which is not an isomorphism. If one exists, the structure hypothesis
supplies smoothness, connectedness and affineness of this same `P`; the
pseudo-parabolic predicate supplies its closed inclusion. The containment
hypothesis gives the required rational conjugation and actual factorization
of every split subtorus through this one inclusion. This is the second
descent branch. If no such inclusion exists, every pseudo-parabolic inclusion
is an isomorphism. The envelope hypothesis then supplies the single smooth
connected affine solvable closed subgroup through which every split subtorus
factors. This is the first branch, where the subgroup may be all of `G`.

`smoothMaximalSplitTorusConjugacy_of_solvable_of_envelope_of_structure_of_containment`
also takes `SolvableMaximalSplitTorusConjugacyStatement` as an explicit
hypothesis. It passes the preceding descent theorem to the published
`smoothMaximalSplitTorusConjugacy_of_solvable_of_descent`, whose proof performs
Noetherian closed-subgroup induction and transports subgroup conjugacy back
to `G`. The result is the exact published
`SmoothMaximalSplitTorusConjugacyStatement`, conditional on all four
prerequisites.

This is internal derived content: its only new argument is the classical
case distinction and the assembly of the existing interfaces. The source
provenance of the structural branches is recorded in the imported statement
modules, and their geometric, fixed-point, lifting and solvable conjugacy
proof obligations remain unchanged. All factorizations are actual
group-scheme homomorphisms over the original field. No perfectness,
infinitude, characteristic or reductivity restriction is introduced, and no
imported Lean or Markdown file is changed.
