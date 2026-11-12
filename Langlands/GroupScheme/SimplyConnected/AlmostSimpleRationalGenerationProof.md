# Rational generation of simply connected groups by almost-simple factors: proof

Authors: Worker 4902.

`Langlands.GroupScheme.simplyConnectedAlmostSimpleRationalGeneration` proves
the unchanged published
`Langlands.GroupScheme.SimplyConnectedAlmostSimpleRationalGenerationStatement.{u}`
from `Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationStatement`,
for arbitrary universe `u`. Its type is exactly that proposition, and it has
no hypotheses.

The proposition says the following. Let `k : Type u` be any field, and let
`G` be a group scheme over `Spec k` with `IsSimplyConnected G`. Let `H` be a
subgroup of `rationalPoints G` that contains `(rationalPoints.map a).range`
for every `a : A ⟶ G` with `IsAlmostSimple A`, `IsClosedSubgroup a` and
`(SubgroupFunctor.range a).IsNormal`. Then `H = ⊤`. The field is arbitrary:
it need not be algebraically closed, perfect or infinite, and it may have
any characteristic. `G` need not be split, quasi-split or isotropic. The
statement and its imported definitions are unchanged.

## Implemented proof

The proof composes published Library theorems. It defines no new mathematics
and adds no premise. It proceeds in five steps, each a `have` in the Lean
proof.

1. `algClosedMaximalTorusCentralizer_fromQuotient` (module
   `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient`)
   proves `AlgClosedMaximalTorusCentralizerFromQuotientStatement.{u}`. Its two
   premises are `DynamicCentralizerReductiveStatement.{u}`, supplied by
   `dynamicCentralizerReductive` (module
   `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`), and
   `SolvableTorusQuotientStatement.{u}`, supplied by `solvableTorusQuotient`
   (module `Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof`).
   The result is `AlgClosedMaximalTorusCentralizerStatement.{u}`: over an
   algebraically closed field, a maximal torus of a connected reductive group
   is its own centralizer, as subgroup functors on every test scheme.

2. `semisimpleRootGenerationReduction` (module
   `Langlands.GroupScheme.Reductive.RootGenerationReduction`) proves
   `SemisimpleRootGenerationReductionStatement.{u}`, which says that
   `RootRankOneFactorizationStatement.{u}` and
   `AlgClosedMaximalTorusCentralizerStatement.{u}` imply
   `SemisimpleRootGenerationStatement.{u}`. The first premise is supplied by
   `rootRankOneFactorization` (module
   `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`) and the
   second by step 1. The result is generation of a semisimple group over an
   algebraically closed field by the root subgroups of a split maximal
   torus, in the closed-subgroup form.

3. `semisimpleAlmostSimpleGeneration_of_rootLines` (module
   `Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction`) has four
   premises:
   - `NormalReductiveCenterStatement.{u}`, supplied by
     `normalReductiveCenter` (module
     `Langlands.GroupScheme.Reductive.NormalCenterProof`);
   - `SemisimpleRootGenerationStatement.{u}`, supplied by step 2;
   - `AbsoluteRootVectorLineStatement.{u}`, supplied by
     `absoluteRootVectorLine` (module
     `Langlands.GroupScheme.Absolute.RootVectorLineProof`);
   - `MaximalTorusConjugacyStatement.{u}`, supplied by
     `maximalTorusConjugacy` (module
     `Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof`).

   It concludes `SemisimpleAlmostSimpleGenerationStatement.{u}`: over an
   algebraically closed field, a closed subgroup of a semisimple group that
   contains every closed normal almost-simple subgroup is the whole group.
   The published assembly first derives the normal-root dichotomy. It then
   applies Lie-dimension induction with a normal almost-simple factor and the
   reduced identity component of its centralizer
   (`semisimpleAlmostSimpleGeneration_of_actualRoots`, module
   `Langlands.GroupScheme.Reductive.AlmostSimpleGenerationReduction`).

4. `semisimpleNormalIsogenyComplement_of_generation` (module
   `Langlands.GroupScheme.Reductive.NormalIsogenyComplementGeneration`)
   turns step 3 into `SemisimpleNormalIsogenyComplementStatement.{u}`. Over
   any field, a smooth connected closed normal subgroup `H` of a semisimple
   group `G` is semisimple. It has a semisimple closed normal complement `K`
   that commutes with `H` on every test scheme. The product `H ⊗ K` is
   semisimple, and the multiplication `H ⊗ K → G` is a central isogeny. The
   published proof derives perfectness of semisimple groups over
   algebraically closed fields from step 3
   (`algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration`, module
   `Langlands.GroupScheme.Derived.AlmostSimplePerfect`). It then constructs
   `K` over the original field as the derived subgroup of the centralizer of
   `H`, and compares with the algebraic closure
   (`semisimpleNormalIsogenyComplement_of_generation_and_perfectness`, module
   `Langlands.GroupScheme.Reductive.NormalIsogenyComplementReduction`).

5. `simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement`
   (module
   `Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationReduction`)
   takes `SemisimpleNormalIsogenyComplementStatement.{u}` and concludes the
   target. The published proof inducts on the Lie dimension of `G`. If `G` is
   trivial or almost simple, the conclusion is immediate. Otherwise there is a
   proper nontrivial smooth connected closed normal subgroup. Step 4 gives a
   complement, and the multiplication from the product is a central isogeny
   from a semisimple group. `IsSimplyConnected G` makes it an isomorphism.
   Both factors are then simply connected and of smaller dimension. The
   induction hypothesis applies to each factor, and the factors together
   give all of `G(k)`.

No step assumes an almost-simple decomposition of `G`, root-group
generation, Milne 21.51, a complement or any other unproved proposition.
Every structural premise of every reduction used is discharged by a
published unconditional theorem. A development check reported only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This proof is an internal composition of published Library results and makes
no new literature claim. The target's paired Markdown records its sources:
J. S. Milne, *Algebraic Groups* (2022 corrected reprint), registered as
`milne-2022-algebraic-groups`, Theorem 21.51 (printed pp.439–441), and
G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem* (1985),
registered as `prasad-raghunathan-1985-kneser-tits`, §1.5 (printed p.108).
The target Markdown's route takes the almost-direct product decomposition of
Milne 21.51 and uses simple connectedness to make the multiplication map an
isomorphism. The implemented route instead uses the published
dimension induction with semisimple normal complements described in step 5,
with the complements built in step 4. It does not construct the full finite
decomposition into almost-simple factors.
