# Term transitivity and the top term on actual rational points

Author: Worker 3940.

This module proves two of the five named inputs of the published reduction
`rationalInvolutivityStatement_of_reductions` in
[`RationalInvolutivityReduction`](RationalInvolutivityReduction.md): term
transitivity and the top term. Both are proved for the actual standard family
of `RationalPoint k G.X`. It also records that involutivity follows from the one input of that
reduction that remains unproved, induction compatibility, and hence from
induced K0 Weyl conjugacy alone. It does not prove involutivity.

All names below have prefix `Langlands.Aubert.General.RationalPointFamily`
unless another namespace is given.

## Term transitivity

`rationalTermTransitivity` has type exactly
`RationalTermTransitivityStatement.{u, v}`, with independent universes `u` and
`v`. It has no additional theorem parameters. The statement quantifies over
every nonarchimedean local field `k : Type u`, including positive
characteristic, and every connected reductive group scheme `G`. It also
quantifies over every maximal split torus `i` and generic cocharacter `ν`, and
over every enumeration of the simple-root subtype, including the empty one.
The canonical `pointTopology` is installed on the rational points. For every
`J : Finset (SimpleRoot i ν)` and `I : Finset J`, the conclusion is

`i_J ∘ (i^{L_J}_I ∘ r^{L_J}_I) ∘ r_J = i_I ∘ r_I`

on the whole exact finite-length Grothendieck group. Here
`i_I ∘ r_I` is the ambient `alternatingTerm` at `leviIndex J I`. The middle
factor is the `I`-th term of the Levi family obtained by the literal
`subgroupOf (levi i ν J)` restrictions.

The proof introduces all of the statement's binders and applies the generic
`inductionK0_comp_leviTerm_comp_jacquetK0` from
[`TermStages`](TermStages.md). The fine decomposition is the actual standard
decomposition at `leviIndex J I`, the coarse decomposition is the one at `J`,
and the inner decomposition is `isSemidirectDecomposition_in_levi`. The Levi
inclusion is `levi_le_of_subset`. The remaining inputs of that lemma are
supplied as follows.

| Input of `inductionK0_comp_leviTerm_comp_jacquetK0` | Supplied by |
| --- | --- |
| Induction in stages, `leviNormalizedInductionFunctor ⋙ i_J ≅ i_I` | `standardInductionStagesIso` from [`RationalInductionStages`](RationalInductionStages.md), at the statement's closed Levi `hM J` and restricted compact-limit premise `hLUc J I` |
| Jacquet restriction in stages, `r_J ⋙ leviNormalizedJacquetFunctor ≅ r_I` | `standardJacquetStagesIso_of_standardProjection` from [`RationalJacquetTransitivity`](RationalJacquetTransitivity.md), at the same premises |
| Ambient finite length and exactness at `J` and at `leviIndex J I` | `standardParabolicFiniteLength` |
| Finite length and exactness of the inner family | `standardLeviParabolicFiniteLength`, from `hM J`, `hLproj J`, `hLUc J`, `hiLFl J` and `hrLFl J` |

Both stage isomorphisms are proved natural isomorphisms of the actual
normalized functors, with both normalizing characters. Their positive Haar
character identity is the proved `standardJacquetModulus_stages` of
[`RationalHaarModulus`](RationalHaarModulus.md). It uses the statement's
continuous standard projections and the second countability of the
rational points that the module derives. No modulus identity, stage
isomorphism or composition law is assumed. `TermStages` composes the two
isomorphisms through the canonical subgroup pullback. It then reads the
composite on exact K0 through `FiniteLengthGrothendieckGroup.map_eq_of_iso`
and `FiniteLengthGrothendieckGroup.map_comp`. The resulting equality is
defined on the whole group, including the relations of nonsplit short exact
sequences.

The statement's finite-length data inside the Levis are Prop-valued. Any
proof of them therefore gives the same Levi term. The conclusion depends only
on the actual functors.

## Top term

`rationalTopTerm` has type exactly `RationalTopTermStatement.{u, v}`, with
no additional theorem parameters. For every enumeration of the simple roots,
the full-index `alternatingTerm` of the actual family is `LinearMap.id` on
the whole exact Grothendieck group. The proof introduces the binders and
applies the published `alternatingTerm_univ_eq_id` of
[`RationalEndpoint`](RationalEndpoint.md).

That theorem evaluates the statement's `StandardCocharacterStatement` premise
at the zero cocharacter, which is standard at the full simple-root set. This
shows that the full-index parabolic and Levi are `⊤`.
`standardUnipotent_simple_eq_bot` shows that the radical is `⊥`.
`endpoint_inductionK0_comp_jacquetK0` of [`Endpoint`](Endpoint.md) then
identifies the actual normalized induction after Jacquet restriction with the
identity functor up to natural isomorphism. Both normalizing characters are
trivial and the coinvariant relations are zero. The theorem holds equally
for an empty simple-root type, where the full index is also the empty index.

## Conditional involutivity

`rationalInvolutivityStatement_of_inductionCompatibility` proves
`RationalInvolutivityStatement.{u, v}` from one explicit hypothesis, the
published target `RationalInductionCompatibilityStatement.{u, v}`. It applies
`rationalInvolutivityStatement_of_reductions` to that hypothesis and to four
proved theorems:

- the published `Langlands.GroupScheme.standardLeviIntersection` of
  [`StandardLeviIntersectionProof`](../../../GroupScheme/Rational/StandardLeviIntersectionProof.md),
  which proves `StandardLeviIntersectionStatement.{u}`;
- the published `rationalLeviFiniteLengthStatement` of
  [`RationalLeviFiniteLengthProof`](RationalLeviFiniteLengthProof.md);
- `rationalTermTransitivity` and `rationalTopTerm` above.

`rationalInvolutivityStatement_of_inductionAssemblyPremises` proves the same
target from `RationalInductionAssemblyPremises.{u, v}`. This is the
conjunction of the published targets `RationalGeometricK0ExpansionStatement.{u, v}`
and `RationalInducedK0WeylConjugacyStatement.{u, v}`. It composes the first
theorem with the published
`rationalInductionCompatibility_of_expansion_and_inducedWeyl` of
[`RationalInductionK0Assembly`](RationalInductionK0Assembly.md).

`rationalInvolutivityStatement_of_inducedK0WeylConjugacy` proves the same
target from the single hypothesis
`RationalInducedK0WeylConjugacyStatement.{u, v}`. It applies the previous
theorem to the pair of that hypothesis and the published
`rationalGeometricK0Expansion` of
[`RationalGeometricK0Expansion`](RationalGeometricK0Expansion.md), which proves
`RationalGeometricK0ExpansionStatement.{u, v}` with no premises.

All three theorems are conditional reductions, not proofs of the involutivity
target. Induction compatibility is Aubert's Theorem 1.7(2), first equation,
printed p.2181. Its intended proof uses the geometric lemma and Weyl
conjugacy of induced classes. The geometric K0 expansion is Aubert's identity
(1.3), and induced K0 Weyl conjugacy is Aubert's identity (1.2). The hypotheses
of the three theorems are not treated as structural assumptions.

## Dependencies

The provenance is internal. The two proved statements are steps of Aubert's
proof of Theorem 1.7(3) on printed p.2183, of `aubert-1995-duality`. They
use transitivity of induction and Jacquet restriction, and `i_S ∘ r_S = id`.
The module adds no literature assertion.

The proofs of `rationalTermTransitivity` and `rationalTopTerm` use no
Langlands classification, character independence, geometric lemma, adjointness
theorem or cuspidal-support theorem. They also use neither Aubert
Proposition 3.2 nor induction compatibility. Their representation-theoretic
content is the actual induction-in-stages and Jacquet-in-stages isomorphisms
and the endpoint comparison. These are built in `InductionStages`,
`JacquetStages` and `Endpoint` from smooth induction in stages, split-quotient
and character-twist equivalences, the localization tower and evaluation at
the identity. The three conditional theorems additionally use `standardLeviIntersection` and
`rationalLeviFiniteLengthStatement`, whose paired Markdown records their
declaration-level dependencies. `standardLeviIntersection` is a group-scheme
statement with no representation-theoretic content.
`rationalLeviFiniteLengthStatement` uses explicit evaluation maps and
covariance, but no adjunction, and invokes no classification or
cuspidal-support theorem. The second and third conditional theorems also use
`rationalInductionCompatibility_of_expansion_and_inducedWeyl`. That theorem
takes the geometric-lemma expansion and induced Weyl conjugacy as hypotheses
and proves neither. The third theorem discharges the expansion by
`rationalGeometricK0Expansion`, the general rational-point geometric lemma on
exact K0. Its paired Markdown records its dependencies: the published
`standardParabolicPointsStatement_proof` (Bruhat indexing of parabolic double
cosets) and the support filtration, with no adjointness, cuspidal-support,
character-independence or classification theorem in its proof bodies.

The local topology is the value `pointTopology`, installed by `let`, exactly
as in the target statements.

The conditional involutivity reductions also use the finite signed-sum
calculation in `Langlands.Aubert.General.InvolutivityReduction`:
`involutivityStatement_of_inductionCompatibility` expands the second operator,
uses `alternatingOperator_comp_alternatingTerm`, and collapses the double sum by
`sum_neg_one_pow_smul_sum_leviIndex`. Its scalar cancellation is
`sum_superset_neg_one_pow_card`, ultimately
`Finset.sum_powerset_neg_one_pow_card`. This computation includes the empty
root type. The third reduction additionally reaches the finite Coxeter
signed-intersection identity through
`rationalInductionCompatibility_of_expansion_and_inducedWeyl`.

For the conditional reductions, the potentially misleading classification and
cuspidal-support module dependencies of the Levi finite-length theorem are the
generic declarations `Langlands.FiniteLengthAssembly.finiteLength_of_surjective`,
`Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff`,
`Langlands.FiniteLengthAssembly.length_comp_surjective`, and
`Langlands.CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`.
They concern arbitrary surjective intertwiners or monoid maps, rather than a
classification or cuspidal-support theorem. The evaluation declarations are
`Langlands.Aubert.General.FirstAdjointness.evaluation` and
`Langlands.Aubert.General.FirstAdjointness.evaluation_covariance`, through
`Langlands.Jacquet.CharacterReciprocity.evaluation`, `evaluation_covariance`
and `evaluation_translate`. These are explicit maps and covariance formulas;
no adjunction theorem is invoked. The paired Markdown of
`RationalLeviFiniteLengthProof` records the corresponding scopes.
