# Rank-one Jacquet computation from ordered actual geometric filtrations

Author: Worker 124.

This module implements the implication

```text
RationalMaximalSourceGeometricFiltrationStatement.{u,v} →
  RationalRankOneGeometricJacquetStatement.{u,v}.
```

The entry is the proof-valued definition
`rationalRankOneGeometricJacquetOfMaximalSourceFiltration`. Its filtration
premise is still unproved. This contribution does not prove the whole host
target or complete Task 5271. All target binders and their universes are
retained, and the target Lean/Markdown pair and its imported pairs are unchanged.

## Actual vanishing away from the self Levi

`pointRankOneOtherProperJacquet_isZero_of_filtration` takes the literal
self-association equality, maximal `J`, arbitrary inside-Levi cuspidal `σ`,
`K ≠ univ`, `K ≠ J`, and a `PointGeometricObjectFiltration` of the original
`r_K(i_J σ)`. For each index, its bijection supplies the actual minimal class;
its lift, class equation and decomposition witnesses are passed unchanged to
`pointRankOneOtherProperTerm_subsingleton`. The actual grade isomorphism
then makes the grade's carrier subsingleton.
`objectRepFiltrationSubsingleton` gives a zero ambient carrier, and
`SmoothRep.isZero_iff_subsingleton_carrier` gives the required zero object.
No finite-length or irreducibility premise enters this step.

## The actual short exact sequence at J

`pointRankOneMiddleSequence_of_filtration` takes the analogous self filtration,
the exact longest-class lift `n`, `hn` and normalization witness `hself` from
the host target. It constructs the actual short exact sequence in the required
direction, without splitting or assuming nonzero endpoints.

First, the inverse-longest class differs from `1`. Otherwise
`positiveSimpleSet_longestRep`, the subset equality and the fact that every
simple root is an ascent of `1` would make `J = univ`, contrary to maximal
properness. `canonical_simpleSurvivorPairs` supplies the inverse-longest
class as a minimal self representative. The filtration's bijection places it
at a unique index `d`. The identity-last condition and the inequality of the
two classes imply that `d` lies in the prefix, giving `q₀ : Fin tailLength`.

The grade at `q₀.castSucc` is identified with the exact
`(conjugationFunctor n⁻¹ _).obj σ` using
`pointRankOneInverseLongestTermIso`. The final grade is identified with `σ`
using `pointGeometricTermIdentityClassIso`, valid for every lift of class one.
For each other prefix index, bijectivity excludes both surviving classes.
`pointRankOneSelfTerm_subsingleton_of_other_class` makes that grade zero.
Then `smooth_shortExact_of_last_and_single_prefix` constructs actual
intertwining maps

```text
0 → (conjugationFunctor n⁻¹ _).obj σ → r_J(i_J σ) → σ → 0.
```

The conjugate acts by `x ↦ σ(n * x * n⁻¹)`, exactly as in the target.
The lower piece is the penultimate subrepresentation, identified by
single-grade collapse; the upper map is the actual last-quotient projection
followed by the identity-grade isomorphism. Thus the proof uses the endpoint
order, not an unordered list of isomorphism classes.

## Whole-scope conditional assembly

The entry introduces exactly the field, group scheme, torus and topology
instances, actual simple-root enumeration, structural statements, closed
families and Coxeter premises of the host target. It derives
`associatedSubset actual J = J` from the supplied `hself` using
`pointAssociatedSubset_eq_of_normalizing_longestLift`. The filtration premise
is applied at the same data and `σ`, first to `J` and then to each other proper
`K`. The two local results provide the target's conjunction.

Both universe parameters are independent and no theorem parameter is hidden
outside the displayed implication. All fields, including positive
characteristic, nonsplit and non-quasisplit groups, remain included. There is
no nonempty-root premise; maximality has no witness when the roots are empty.

## Provenance and dependency boundary

This is an internal algebraic assembly of the published target and the
explicit new ordered-filtration proposition. The finite-filtration sequence
lemma is documented in
[LastAndSinglePrefixSequence](../../Filtration/LastAndSinglePrefixSequence.md).
The term calculations and their structural and normalization dependencies are
documented in [RationalRankOneGeometricTerms](RationalRankOneGeometricTerms.md).
Other directly invoked declarations are `IsMaximalStandard.ne_univ`,
`positiveSimpleSet_longestRep`, `canonical_simpleSurvivorPairs`,
`mem_simpleSurvivorPairs`, `mem_minimalReps`,
`pointGeometricTermIdentityClassIso`, `Representation.equivOfIso`,
`objectRepFiltrationSubsingleton`, and
`SmoothRep.isZero_iff_subsingleton_carrier`.

The proof uses the geometric lemma only as the explicit, unproved
`RationalMaximalSourceGeometricFiltrationStatement` premise. It does not invoke
a proved instance of the represented or rational geometric lemma. No
adjointness, cuspidal-support theorem, character independence or classification
result is used in the proof bodies or in the documented term dependencies.
The host target's imported closure includes separate statements and
conditional rank-one constituent assemblies; importing them does not
instantiate their representation-theoretic hypotheses. No Grothendieck-class
identity is used to infer a representation isomorphism or zero object.

To obtain the task's required theorem with no extra parameters, the
ordered-filtration proposition must have an exact published proof under its
visible premises (or a different route must establish the target directly).
Its publication as a statement or acceptance of this implication does not
satisfy that obligation.
