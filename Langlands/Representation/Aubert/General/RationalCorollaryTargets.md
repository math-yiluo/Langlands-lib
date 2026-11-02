# Corollary 1.10 on the actual rational-point family

Author: Worker 1186. The five universally quantified propositions specialize
`GeneralCorollaryTargets` using Worker 165's actual standard rational-point
families, decomposition and operator adapters. No instance of the corollary
or any representation-theoretic prerequisite is proved here.

The field is any nonarchimedean local field. The group scheme is connected
reductive, the torus map is an actual maximal split torus, and the
cocharacter is generic. `SimpleRoot i ν` consists of the actual simple
relative characters. The subgroup families are literally the existing
standard parabolic, Levi and unipotent point subgroups at the character
subset `rootSet i ν I`. The ambient topology is the canonical evaluation
topology `pointTopology`, with explicit local compactness,
nonarchimedean-group and Hausdorffness premises. There is no
characteristic-zero, split, quasisplit or positive-rank restriction.

`StandardCocharacterStatement` supplies the comparisons from which the
ambient semidirect decompositions are derived. `StandardLeviIntersectionStatement`
supplies the all-test intersection decomposition. The imported
`isSemidirectDecomposition_in_levi` evaluates that statement and restricts
the result to the actual Levi point subgroup. For `I : Finset J`,
with `K = leviIndex J I`, the inside-Levi family is exactly
`P_K.subgroupOf L_J`, `L_K.subgroupOf L_J` and `U_K.subgroupOf L_J`.
There is no free inside-Levi decomposition hypothesis or second
root-labeling family. Closedness of each actual Levi and each unipotent
subgroup remains explicit. The root-system premise gives the finite
simple-root enumeration through `simpleRelativeRootFintype`.

The generic `IsCorollaryLeviCuspidal` therefore tests the actual normalized
inside-Levi Jacquet modules for every proper `I`, requiring each to be a
zero object. This is an object-level condition. All representations are
actual smooth complex representations with carriers in
`Type (max (u + 1) v)`; finite-length objects include their actual length
witnesses. The K0 quotient imposes all actual short exact sequence relations.

| Declaration in `RationalPointFamily` | Exact target |
| --- | --- |
| `RationalCorollary110aStatement` | If `σ` of `L_J` is irreducible and cuspidal and its actual normalized induction is irreducible, then `D_G[i_J σ] = (-1)^|J| [i_J σ]`. The source induction-irreducibility premise is retained. |
| `RationalCorollary110bStatement` | For `J = univ.erase α`, reducible actual induction of irreducible cuspidal `σ` has two irreducible composition factors and both equations `(-1)^|J| D_G[ρplus] = [ρminus]` and `(-1)^|J| D_G[ρminus] = [ρplus]`. |
| `RationalRankOneLengthTwoStatement` | The same reducibility hypotheses imply an actual length-two composition series, independently of the signed-exchange conclusion. |
| `RationalRankOneSelfAssociationStatement` | The same hypotheses force `associatedSubset actual J = J`, and every actual normalizer lift of the specified longest representative normalizes the actual `L_J`. |
| `RationalRankOneJacquetModulesStatement` | For every specified longest lift and its actual self-normalization witness, there are two irreducible factors with `r_J ρplus ≅ σ`, `r_J ρminus ≅ Ad(n⁻¹) σ`, and both Jacquet modules zero for every other proper standard subset. |

`HasTwoConstituents` is the existing actual short exact sequence predicate
in either factor order. It assumes no splitting or semisimplicity.
The second Jacquet module uses `conjugationFunctor n⁻¹`, so its action is
exactly `x ↦ σ(n*x*n⁻¹)`. The quantifier retains every normalizer lift of
the source's constructed longest element of `D(J,∅)`. The Jacquet
prerequisite supplies the labeling of the two factors; the exchange
conclusion is symmetric in them.

The two corollary statements use `standardParabolicFiniteLength`.
Their additional explicit premises are closed parabolic point subgroups,
continuous standard projections, compact-limit unipotent subgroups and
separate finite-length preservation by normalized induction and Jacquet
restriction. Existing exactness theorems derive the other parts of
`ParabolicFiniteLength`. The three separately named rank-one prerequisites
need no such K0-map/exactness premises and do not quantify them.

For the two targets using Weyl indexing, the quotient is the actual
normalizer of the torus-point image divided by its full centralizer.
Finiteness of that actual quotient remains explicit. The actual Coxeter
system is indexed by the literal simple roots. Its connection to the root
action is required by both `RootLengthComparison` and
`PositiveSimpleReflectionComparison`, using the separate exact
scheme-to-point normalizer and centralizer comparisons. The generated
standard Coxeter subgroups must equal the images of the actual Levi Weyl
quotients through `actualLeviWeylIdentification`. The named intrinsic
`minimalityLengthCriterion` and `associatedSubsetLaws` are explicit inputs.
Under these root-sign and intrinsic inputs the imported
`rootSet_associatedSubset` identifies the associated subset with the
actual inverse-longest root image. Thus the indexing is tied to the source
root action rather than a free Coxeter relabeling. These are intermediate
premises, not proofs or classifications of allowed final external inputs.

Part (a) allows every `J`, including the empty set and empty simple-root
type. In part (b) and the rank-one prerequisites there is no maximal label
when the simple-root type is empty, so those conclusions are vacuous.
The sign is always `(-1)^|J|` with the unadjusted operator. The operator's
empty-root sum has its single empty-subset term.

The provenance is a derived specialization of Aubert 1995, Corollary 1.10
and its proof on printed p.2183, using the cuspidality definition on
p.2181. The separate length and self-association targets follow the
prerequisite route cited there to Casselman 1995, section 7.1,
Corollary 7.1.2 and Theorem 7.1.4, printed pp.67–68. The full
source-to-generic-declaration and sign discussion is in
`../GeneralCorollaryTargets.md`. These are target formulations; the
general deductions from Casselman remain unproved here.

Parent `46df6a68-5db4-4428-8044-05151d6ce1f6` retains the proof successors:
induction compatibility and the Levi cuspidal eigenvalue for (a), and
length two, self-association, the Jacquet pattern, exact-K0 additivity,
the actual top term and induced-K0 Weyl-conjugacy for (b). The latter is
the separate representation-theoretic input in
`RationalInducedWeylConjugacyTarget`; a Ban–Jantzen proof must record actual
general character-independence, Langlands-classification and geometric-lemma
declarations. No representation-theoretic premise is moved into the
external Chapter V boundary. Aubert Proposition 3.2 is unused.

Only this Lean/Markdown pair is selected for publication. The imported
restricted-Levi decomposition retains Worker 165's separate review and
publication; its presence in a validation snapshot grants neither here.
