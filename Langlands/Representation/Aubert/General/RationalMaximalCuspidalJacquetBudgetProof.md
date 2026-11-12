# The coatom Jacquet-length budget on actual reductive rational points

Author: Worker 153.

The declaration is

```text
Langlands.Aubert.General.RationalPointFamily.rationalMaximalCuspidalJacquetBudget :
  Langlands.Aubert.General.RationalPointFamily.RationalMaximalCuspidalJacquetBudgetStatement.{u,v}
```

It proves the whole unchanged proposition, with independent universes `u,v`
and no parameters outside it. The field is every nonarchimedean local field,
including positive characteristic. The connected reductive group may be
nonsplit or non-quasisplit. The group consists of the actual rational points
with canonical `pointTopology`; labels are literally `SimpleRoot i ν`, and
representation carriers have universe `max (u + 1) v`. The actual normalized
induction and Jacquet functors and the original inside-Levi cuspidality
predicate are retained. All standard-cocharacter, standard-Levi-intersection,
relative-root, topology and closedness premises are exactly those of the target.

The supporting declaration
`rationalMaximalCuspidalJacquetBudget_of_maximalSourceFiltration` proves the
closed implication from `RationalMaximalSourceGeometricFiltrationStatement`
to this whole target. The final declaration applies it to the published
`rationalMaximalSourceGeometricFiltration` at the same independent universes.
The argument below describes that implication and how the filtration theorem
discharges its premise. This is an internal composition of published results;
no new original-literature assertion is introduced.

## Discharging the point and Coxeter inputs

Introduce exactly the target's quantified data. `rationalWeylComparison`
produces `HasPointNormalizerComparison` and `HasPointCentralizerComparison`.
It specializes `GroupScheme.normalizerPointsInfiniteField` to the infinite
local field; the full centralizer is retained.

`rootSpanPointCoxeterData` constructs one finite actual Weyl Coxeter system on
the same simple-root labels. Its `finiteWeyl`, `system`, `rootLength` and
`leviWeyl` fields supply finite enumeration, root-sign length, and the actual
standard-Levi Weyl identification. They all refer to the same system.
`positiveSimpleReflectionComparison_of_rootLength` proves its positive
simple-reflection law. The intrinsic `minimalityLengthCriterion_proof` and
`associatedSubsetLaws_proof` give its remaining finite Coxeter laws. These
are deductions from the original target data, rather than additional premises.

## Actual filtrations for every coatom

Apply the proved `rationalMaximalSourceGeometricFiltration` to this system,
the given maximal source `J`, the original smooth `σ`, and each target
`I = univ.erase a`. `Finset.erase_ne_self` proves the target is proper. The
filtration theorem allows every maximal source and proper target, so it
applies in both association cases without a normalization witness.

Choose its actual `PointGeometricObjectFiltration` for every literal label
`a`. Its enumeration bijects `Fin (tailLength + 1)` with `minimalReps`;
composing with subtype value gives an injective list of minimal Weyl classes.
The actual lifts and their quotient-class equations, source and target
semidirect decompositions, zero-to-full `ObjectRepFiltration`, and every
actual grade isomorphism are the fields supplied by that datum. They feed
directly into `pointCoatomJacquetBudget_of_geometricFiltrations`. The datum's
identity-last refinement is available but is not required by this length sum.

## Actual lengths and occurrence count

The last helper rewrites the maximal source as `univ.erase b` and uses
`repLength_eq_sum_of_filtration` and `repLength_congr` to compute the actual
Jacquet length as the sum of lengths of all its original grades.
`pointGeometricTerm_repLength` makes every grade length zero or one.

For a proper source intersection,
`pointCuspidalGeometricTermVanishing_of_rootComparisons` applies the original
`IsCorollaryLeviCuspidal` predicate, with its literal
`isSemidirectDecomposition_in_levi`, and gives a subsingleton carrier. For a
full source intersection, source and target coatoms have equal cardinality.
`rootImage_eq_of_full_intersection` gives an actual root association,
`pointGeometricTermRootAssociationIso` identifies the term with Levi
conjugation pullback of `σ`, and `smooth_isIrreducible_of_iso_pullback`
transports irreducibility. `repLength_eq_zero_iff` and
`repLength_eq_one_iff` give the two lengths in `ℕ∞`.

`coatomFullSourceIndicatorBudget` counts all surviving occurrences. The sigma
`coatomFullSourceIndices` retains the literal target label and its grade
index. It maps `(a,q)` to `(univ.erase a,w a q)` in `fullIntersectionPairs`.
`Finset.erase_inj` recovers `a`, and injectivity of each original enumeration
recovers `q`. `card_fullIntersectionPairs_coatom_le_two` bounds that original
pair set by two. Thus no multiplicity is lost. The resulting bound is the
sum of the original coatom Jacquet lengths in `ℕ∞`; it also excludes infinite
length of each term. No finite-length-preservation hypothesis is used.
If the simple-root type is empty, maximality has no witness and the statement
is vacuous, without adding a positive-rank premise.

## Transitive geometric-lemma dependencies

The geometric lemma enters through the proved
`rationalMaximalSourceGeometricFiltration` from
[RationalRankOneGeometricJacquetProof](RationalRankOneGeometricJacquetProof.md).
That supporting proof applies `pointGeometricObjectFiltrationOfEpsilonBalance`
and discharges its correction premise with `geometricEpsilon_mul_eq_one`.
Closed parabolics and continuous Levi projections come from
`isClosed_standard_parabolic` and `continuous_standard_projection`.

The actual construction uses `pointMinimalOrbitOrderingIdentityLast`,
`minimalOrbitOrdering` and
`GroupScheme.standardParabolicPointsStatement_proof` for the bijection with
actual double cosets and the finite open-initial-union orbit order. The point
Bruhat result is proved from `rationalBruhat` and `rootRankOneFactorization`.
`pointSourceIntersectionIdentities` and
`geometricIntersectionDecompositions_of_pointSource` give the literal
intersection decompositions. The actual radicals are limits of compact
subgroups by
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.

`jacquetSupportFiltration`, evaluated at the original `σ`, constructs the
actual filtration. `jacquetSupportGeometricTermIso` identifies its grades by
composing `jacquetSupportOrbitIso`, `orbitPieceCoinvariantsIso`,
`geometricNormalizedCompactSourceRepIso`,
`geometricNormalizedCompactActualNatIso` and `geometricEpsilonCompactTermIso`.
This route uses exact radical coinvariants and the compact Mackey support
filtration. `compactSpace_leftQuotient_geometricTarget`, through
`BruhatTits.dynamicParabolicQuotientCompact`, proves target quotient
compactness, permitting `Induction.compactSmoothIso`. All extra closedness,
continuity, compact-limit and orbit premises are discharged as above.

`geometricEpsilon_mul_eq_one` proves cancellation on the entire actual common
Levi for every lift. It factors the two Haar corrections into five actual
positive Haar moduli and applies
`centralizingHaarCharacter_correctionProduct_eq_one_of_characterRestrict_injective`
on a represented dynamic centralizer. Its restriction injectivity is proved
from `leviSplitComponentStatement`, `splitComponentStatement` and
`centralSplitTorusCharacter`; the resulting identity is transported to the
literal common Levi. The character injectivity here concerns algebraic
rational characters of a connected reductive group.

This is an internal composition of the published constructions described in
[RationalCoatomGeometricBudget](RationalCoatomGeometricBudget.md),
[RationalGeometricObjectFiltrationConstruction](RationalGeometricObjectFiltrationConstruction.md),
[RationalGeometricOrbitTerm](RationalGeometricOrbitTerm.md),
[ParabolicSupportFiltration](ParabolicSupportFiltration.md) and
[RationalGeometricEpsilonBalance](RationalGeometricEpsilonBalance.md).
The named proof bodies use no adjointness, cuspidal-support theorem,
independence of representation characters or Langlands classification.
The broader imported closure contains other targets and conditional
assemblies whose unproved hypotheses are not invoked. No Grothendieck-class
identity or Aubert Proposition 3.2 is proof evidence for this actual-length
argument.
