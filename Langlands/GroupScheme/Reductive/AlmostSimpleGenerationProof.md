# Generation of semisimple groups by normal almost-simple subgroups: proof

Worker 4565 assembled this proof.

`Langlands.GroupScheme.semisimpleAlmostSimpleGeneration` proves exactly the
existing `Langlands.GroupScheme.SemisimpleAlmostSimpleGenerationStatement.{u}`
at arbitrary universe `u`. For every algebraically closed field `k : Type u`
of arbitrary characteristic, every semisimple group scheme `G` over
`Spec k`, and every closed subgroup `d : D ⟶ G`, it gives

```text
(∀ A (a : A ⟶ G), IsAlmostSimple A → IsClosedSubgroup a →
    (SubgroupFunctor.range a).IsNormal →
    SubgroupFunctor.range a ≤ SubgroupFunctor.range d) →
  SubgroupFunctor.range d = ⊤.
```

Almost-simplicity is the published corrected `IsAlmostSimple`. Normality,
containment, and fullness are the full subgroup-functor notions, quantified
over every test scheme, including nonreduced tests. No smoothness,
connectedness, or normality of `D` is assumed. The statement and its imported
definitions are unchanged.

## Implemented proof

The Lean proof is a single term composing published theorems; it adds no
new lemma and leaves no structural premise.

1. The published conditional assembly
   `semisimpleAlmostSimpleGeneration_of_rootLines`
   (`Reductive/NormalRootDichotomyReduction.lean`) derives the exact
   `SemisimpleAlmostSimpleGenerationStatement.{u}` from four statements at
   the same universe: `NormalReductiveCenterStatement`,
   `SemisimpleRootGenerationStatement`, `AbsoluteRootVectorLineStatement`,
   and `MaximalTorusConjugacyStatement`. It obtains the normal-root
   dichotomy from actual one-dimensional root lines and maximal-torus
   conjugacy, then runs the Lie-dimension induction of
   `semisimpleAlmostSimpleGeneration_of_actualRoots`
   (`Reductive/AlmostSimpleGenerationReduction.lean`).
2. `normalReductiveCenter` (`Reductive/NormalCenterProof.lean`) supplies the
   full-centre containment for closed normal connected reductive subgroups.
3. `SemisimpleRootGenerationStatement` is supplied by
   `semisimpleRootGenerationReduction`
   (`Reductive/RootGenerationReduction.lean`) applied to two published
   proofs:
   - `rootRankOneFactorization`
     (`Rational/RootRankOneFactorizationProof.lean`), the relative-root
     rank-one factorization statement;
   - `algClosedMaximalTorusCentralizer_fromQuotient`
     (`Absolute/MaximalTorusCentralizerFromQuotient.lean`) applied to
     `dynamicCentralizerReductive`
     (`Dynamic/CentralizerReductiveProof.lean`) and `solvableTorusQuotient`
     (`Absolute/SolvableTorusQuotientProof.lean`). This proves
     `AlgClosedMaximalTorusCentralizerStatement`, the all-test equality of
     a maximal torus centralizer with the torus range over an algebraically
     closed field.
4. `absoluteRootVectorLine` (`Absolute/RootVectorLineProof.lean`) supplies
   an actual closed one-dimensional vector-group representative of each
   intrinsic root functor of a split maximal torus.
5. `maximalTorusConjugacy` (`Absolute/MaximalTorusConjugacyProof.lean`)
   supplies rational conjugacy of maximal tori in smooth connected affine
   groups over an algebraically closed field.

`lean_check` of `Langlands.GroupScheme.Reductive.AlmostSimpleGenerationProof`
reports no errors or warnings, and the theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Provenance

The provenance is internal composition of published Library results. The
target statement documents its source: J. S. Milne, *Algebraic Groups*
(2017), registered as `milne-2017-algebraic-groups`, the generation
consequence of the first assertion of Theorem 21.51 (printed pp.440–441),
with the official errata (`milne-2017-algebraic-groups-errata-2026-11-02`)
correcting Definition 19.7. The implemented route does not follow Milne's
proof. It uses the published root-functor dichotomy and Lie-dimension
induction instead. It does not construct the finite almost-simple
decomposition, pairwise commutation, or finite multiplication kernel of
Theorem 21.51.
