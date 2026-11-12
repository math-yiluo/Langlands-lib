# An initial radical torus with a rational Levi as its ambient centralizer

Authors: Worker 117 and Worker 3483 (named Worker 15 in the route note).
Worker 3483 supplied the composition route; Worker 117 instantiated it with
the canonical published proofs.

`Langlands.GroupScheme.parabolicRadicalTorusInitialCentralizerLevi` proves
exactly
`Langlands.GroupScheme.ParabolicRadicalTorusInitialCentralizerLeviStatement.{u}`,
defined in
`Langlands.GroupScheme.Rational.ParabolicRadicalTorusCentralizerLeviReduction`,
at the published arbitrary universe `u`, with no additional hypotheses.

For every field, connected reductive `G`, parabolic `j : P ⟶ G` and supplied
geometric solvable radical `r : R ⟶ P`, there exist a maximal torus
`sR : S.toGrp ⟶ R` and a rational Levi `l : L ⟶ P` such that the ambient
composite `l ≫ j` represents `torusCentralizer (sR ≫ r ≫ j)`. This is the
whole-torus centralizer on every relative test scheme. The witness includes
the full rational Levi predicate, hence a complementary geometric unipotent
radical and the actual Levi-first multiplication isomorphism.

The proof applies the published reduction
`Langlands.GroupScheme.parabolicRadicalTorusInitialLevi_of_dynamic` from
`Langlands.GroupScheme.Rational.ParabolicRadicalTorusInitialLevi`. Every input
theorem is a published unconditional proof:

| Input theorem | Module |
| --- | --- |
| `Langlands.GroupScheme.parabolicDynamic` | `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` |
| `Langlands.GroupScheme.dynamicCentralizerReductive` | `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof` |

The reduction chooses a cocharacter for the supplied parabolic, constructs
its represented dynamic centralizer and uses connected reductivity to make
it an actual rational Levi. The cocharacter's central split-torus image
factors into the specified solvable radical and extends there to a maximal
torus. Centrality in the Levi and factorization of the cocharacter through
this torus identify its whole ambient centralizer with the same Levi. Both
structural premises are discharged at universe `u`.

This is derived content composed from the named Library results and the
published route notes. Its implemented proof is the initial-torus dynamic
reduction, whose paired Markdown explains the construction and provenance.
The theorem retains every field, characteristic, supplied radical and
universe quantified by the target. It chooses one suitable maximal torus
for each supplied radical; it asserts no extra conclusion for every torus
in that radical.
