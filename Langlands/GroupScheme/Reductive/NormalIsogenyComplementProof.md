# Semisimple normal complements over an arbitrary field: proof

Worker 4955 assembled this proof.

`Langlands.GroupScheme.semisimpleNormalIsogenyComplement` proves the existing
`Langlands.GroupScheme.SemisimpleNormalIsogenyComplementStatement.{u}` exactly,
for an arbitrary universe `u`. The theorem has no further hypotheses. The
setting is any field `k : Type u`, of any characteristic and with no
perfectness, splitting, isotropy or algebraic-closure assumption. Let `G` be a
semisimple group scheme over `Spec k`. Let `j : H ⟶ G` be a closed subgroup
with `H` smooth and connected and `SubgroupFunctor.range j` normal. The
theorem proves that `H` is semisimple. It also produces a semisimple `K` and a
closed subgroup `i : K ⟶ G` with these properties:

- `SubgroupFunctor.range i` is normal.
- The images of `H` and `K` commute on every test scheme over `Spec k`.
- The cartesian product `H ⊗ K` is semisimple.
- `commutingSubgroupMultiplicationHom j i hc` is an `IsCentralIsogeny`.

Being a central isogeny means that the morphism is finite, flat, surjective
and locally of finite presentation, with a central full scheme-theoretic
kernel. Normality and commutation are the published all-test notions,
including nonreduced test schemes. Neither the kernel nor the intersection of
the factors is claimed to be smooth. The statement module and its imports are
unchanged.

## Implemented proof

The Lean proof is a single term made of published theorems. It adds no new
lemma, and no structural premise remains.

1. `semisimpleNormalIsogenyComplement_of_generation`
   (`Reductive/NormalIsogenyComplementGeneration.lean`) proves the exact
   target from `SemisimpleAlmostSimpleGenerationStatement.{u}` alone. From
   that premise it derives perfectness of semisimple groups over
   algebraically closed fields, through
   `algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration`
   (`Derived/AlmostSimplePerfect.lean`). It then applies the assembly
   `semisimpleNormalIsogenyComplement_of_generation_and_perfectness`
   (`Reductive/NormalIsogenyComplementReduction.lean`). That assembly proves
   that `H` is semisimple using unconditional normal-subgroup semisimplicity.
   It takes `K` to be a closed representative of the full derived subgroup of
   a closed representative of the full centralizer of `H`, over the original
   field. After base change to an algebraic closure, generation gives a flat
   surjective multiplication from `H` and the reduced identity component of
   the centralizer. Perfectness identifies that component with the base
   change of `K`. Field-extension reflection then gives semisimplicity of `K`
   and surjectivity of the original multiplication. The finite full centres
   of `H` and `K` give the central-isogeny property and the semisimplicity of
   `H ⊗ K`.
2. `semisimpleAlmostSimpleGeneration_of_rootLines`
   (`Reductive/NormalRootDichotomyReduction.lean`) proves
   `SemisimpleAlmostSimpleGenerationStatement.{u}` from four statements at
   the same universe:
   - `NormalReductiveCenterStatement`, supplied by `normalReductiveCenter`
     (`Reductive/NormalCenterProof.lean`);
   - `SemisimpleRootGenerationStatement`, supplied by
     `semisimpleRootGenerationReduction`
     (`Reductive/RootGenerationReduction.lean`) applied to
     `rootRankOneFactorization`
     (`Rational/RootRankOneFactorizationProof.lean`) and to
     `algClosedMaximalTorusCentralizer_fromQuotient`
     (`Absolute/MaximalTorusCentralizerFromQuotient.lean`). The latter is
     itself applied to `dynamicCentralizerReductive`
     (`Dynamic/CentralizerReductiveProof.lean`) and `solvableTorusQuotient`
     (`Absolute/SolvableTorusQuotientProof.lean`);
   - `AbsoluteRootVectorLineStatement`, supplied by `absoluteRootVectorLine`
     (`Absolute/RootVectorLineProof.lean`);
   - `MaximalTorusConjugacyStatement`, supplied by `maximalTorusConjugacy`
     (`Absolute/MaximalTorusConjugacyProof.lean`).

   Each named proof is an unconditional published theorem whose type is its
   statement at universe `u`. The assembly obtains the normal-root dichotomy
   from actual one-dimensional root lines and maximal-torus conjugacy. It
   then runs the Lie-dimension induction of
   `semisimpleAlmostSimpleGeneration_of_actualRoots`
   (`Reductive/AlmostSimpleGenerationReduction.lean`).

`lean_check` of `Langlands.GroupScheme.Reductive.NormalIsogenyComplementProof`
in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` reports no errors or
warnings. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The second step's composite term for
`SemisimpleAlmostSimpleGenerationStatement` is the same as the one in the
separately submitted proof `semisimpleAlmostSimpleGeneration` (candidate
`30d0d06b-46d4-4595-a4fd-131c13451669`). That module is not yet in the
Library, so this proof repeats the term rather than importing it.

## Provenance

The proof composes published Library results. The target's Markdown records
its source: J. S. Milne, *Algebraic Groups*, corrected reprint 2022
(registered as `milne-2022-algebraic-groups`), Theorem 21.51 and Corollary
21.52, printed pp.439–441 / PDF pp.450–452. Theorem 21.51 states that a
semisimple group is the almost-direct product of its almost-simple normal
subgroups. It also states that every smooth connected normal subgroup is the
product of the factors it contains and is centralized by the others.
Corollary 21.52 states that smooth connected normal subgroups of semisimple
groups are semisimple. The author's errata for the 2022 reprint
(`milne-2022-algebraic-groups-errata-2026-11-04`) contain no correction to
either result.

The Lean proof does not follow Milne's route through a finite decomposition
into almost-simple factors. Its complement is the full derived subgroup of the
full centralizer of `H`, not a product of named factors. Generation by normal
almost-simple subgroups is used only after base change to an algebraic
closure. The central-isogeny conclusion comes from finiteness of the full
centres, not from a finite intersection of factors.
