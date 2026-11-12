# Commuting normal complements in semisimple groups: proof

Worker 4409.

`Langlands.GroupScheme.semisimpleNormalComplement` proves exactly the published
`Langlands.GroupScheme.SemisimpleNormalComplementStatement.{u}`
(`Reductive/SemisimpleNormalComplementStatement.lean`) at an arbitrary universe
`u`. Let `k : Type u` be an algebraically closed field of any characteristic,
`G` a group scheme over `Spec k` with `IsSemisimple G`, and `j : H ⟶ G` a
closed subgroup with `H` smooth, `H.X.left` connected and
`SubgroupFunctor.range j` normal. The theorem gives a group scheme `K` and a
homomorphism `i : K ⟶ G` with these properties. `i` is a closed subgroup and
`SubgroupFunctor.range i` is normal. For every scheme `T` over `Spec k`, every
`x : T ⟶ H.X` and every `y : T ⟶ K.X`, the points `x ≫ j.hom.hom` and
`y ≫ i.hom.hom` commute. The underlying scheme morphism
`(subgroupMultiplication j i).left` is flat and surjective. The statement and
the modules it imports are unchanged, and no hypothesis is added.

## Implemented proof

The Lean proof is a single term that composes published Library theorems. It
adds no new lemma. From the outside in:

1. `semisimpleNormalComplement_of_almostSimpleGeneration`
   (`Reductive/SemisimpleNormalComplementConstruction.lean`) proves the target
   from `SemisimpleAlmostSimpleGenerationStatement.{u}`. Its complement `K` is
   the full closed normal centralizer of `j` from `closedNormalCentralizer`.
   That centralizer is closed, normal on every test scheme and commutes with
   `H` on every test scheme; it need not be smooth. The commuting
   multiplication `H × K → G` is an actual homomorphism whose underlying
   morphism is `subgroupMultiplication j i`. Every closed normal almost-simple
   subgroup of `G` lies either in `H` or in `K`
   (`IsAlmostSimple.range_le_or_commute_of_normal`, which uses the corrected
   definition `IsAlmostSimple`). Hence it lies in the range of the
   multiplication. `flat_surjective_of_contains_almostSimple_factors` then uses
   generation to make the affine schematic image of the multiplication equal
   to `G`. The published `DominantHom.flat_surjective` gives flatness and
   surjectivity.
2. `semisimpleAlmostSimpleGeneration_of_rootLines`
   (`Reductive/NormalRootDichotomyReduction.lean`) proves
   `SemisimpleAlmostSimpleGenerationStatement.{u}` from four statements:
   `NormalReductiveCenterStatement.{u}`, `SemisimpleRootGenerationStatement.{u}`,
   `AbsoluteRootVectorLineStatement.{u}` and `MaximalTorusConjugacyStatement.{u}`.
   It derives the normal-root dichotomy from them. It then argues by strong
   induction on the Lie dimension, using minimal normal almost-simple factors
   and their reduced centralizer cores
   (`Reductive/AlmostSimpleGenerationReduction.lean`,
   `Reductive/MinimalNormalFactor.lean`).
3. The four inputs come from these published unconditional theorems:
   - `normalReductiveCenter` (`Reductive/NormalCenterProof.lean`);
   - `semisimpleRootGenerationReduction`
     (`Reductive/RootGenerationReduction.lean`), applied to
     `rootRankOneFactorization`
     (`Rational/RootRankOneFactorizationProof.lean`) and to
     `algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
     solvableTorusQuotient`
     (`Absolute/MaximalTorusCentralizerFromQuotient.lean`,
     `Dynamic/CentralizerReductiveProof.lean`,
     `Absolute/SolvableTorusQuotientProof.lean`). The last term proves
     `AlgClosedMaximalTorusCentralizerStatement.{u}`, and
     `normalReductiveCenter` uses the same term internally;
   - `absoluteRootVectorLine` (`Absolute/RootVectorLineProof.lean`);
   - `maximalTorusConjugacy` (`Absolute/MaximalTorusConjugacyProof.lean`).

Each leaf is a published unconditional theorem. The final theorem therefore
assumes none of the following as a hypothesis: the almost-simple
decomposition, root-group generation, or faithful flatness of the
multiplication. A development `lean_check` of this module in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` reported no errors or warnings. It
reported only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Normality, containment and commutation are proved directly on every scheme
over `Spec k`, including nonreduced test schemes. The centralizer is defined
by commutation on all test schemes and all their refinements. The
almost-simple dichotomy and the generation argument work with the full
subgroup functors throughout. So the route never passes through statements
about `k`-algebras, and no separate Zariski-gluing comparison with Milne's
functorial formulation is needed.

## Provenance

The theorem composes published Library results only. The statement's
Markdown gives its source: J. S. Milne, *Algebraic Groups* (2017), registered
as `milne-2017-algebraic-groups`, Theorem 21.51 (normal-subgroup part),
printed pp. 440–441 / PDF pp. 456–457. The implemented route does not
reproduce Milne's printed argument. It takes the full scheme-theoretic
centralizer as the complement and obtains flatness from schematic dominance.
The Markdown of each composed module documents its own provenance. The same
composite route appears in the context of task
`043f2527-205c-4cfc-b9b2-553de1010d9d` and inside Worker 4293's staged host
proof candidate `38ce4509-da80-4988-9a72-9f35313ed9e3`. This module states it
separately for the exact complement target.
