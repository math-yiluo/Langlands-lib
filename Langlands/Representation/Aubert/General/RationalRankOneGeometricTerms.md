# Rank-one geometric terms for a self-associated maximal Levi

Author: Worker 124.

This internal supporting unit proves the term calculations needed by
`RationalRankOneGeometricJacquetStatement`. It supplies no geometric filtration
and does not prove that whole statement. The target and its imported pairs are
unchanged. No irreducibility, finite length, admissibility or reducibility of the
inducing object is assumed.

## Finite Coxeter calculation

In `Langlands.Group.RelativeWeylIndexing`, `card_le_of_mapsIntoSimple` proves
`I.card ≤ J.card` from `MapsIntoSimple cs w I J`. Choose for each source label
the target label of its conjugated simple reflection. This function is injective:
equality of target labels gives equality of conjugated reflections, cancellation
gives equality of source reflections, and `simple_injective` gives equality of
labels. The finite-subtype cardinal inequality gives the claim.

`coatom_fullIntersection_classification_of_proper` takes a coatom source
`univ.erase b`, any proper target `I`, a minimal representative `w`, and fullness
of `intersectionSubset cs I (univ.erase b) w`. The published
`intersectionSubset_eq_source_iff_mapsIntoSimple` gives the simple-preserving
condition. The preceding cardinal bound and properness of `I` force equal
cardinalities. The published `coatom_simpleSurvivor_classification` then gives
exactly the pairs `(I,w) = (univ.erase b,1)` or
`(associatedSubset cs (univ.erase b), (longestRep cs (univ.erase b))⁻¹)`.
The Lean proof explicitly reconciles the decidable equality used for `erase`
with the classical one in the published classification. It does not identify a
root with its negative or use reflection conjugacy to infer root positivity.

## Actual rational-point terms

All the following names are in
`Langlands.Aubert.General.RationalPointFamily`. Their group is the actual
`RationalPoint k G.X`, with canonical `pointTopology`, and their labels and
subgroups are literally `SimpleRoot i ν`, `parabolic i ν`, `levi i ν` and
`unipotent i ν`. The field and carrier universes are independent; the smooth
objects have carriers in `Type (max (u + 1) v)`. The term-vanishing results
need only a topological field and the displayed actual-group and structural
premises, so apply in particular at every local field in the target.

`pointAssociatedSubset_eq_of_normalizing_longestLift` uses the existing
standard-cocharacter, root-sign, minimality, association and actual Levi Weyl
identification premises. `associatedLeviConjugation_of_standard`, after
`standardLeviConjugationStatement_of_standardCocharacterStatement`, supplies
actual associated-Levi conjugation. The published
`associatedSubset_eq_of_longestLift_normalizes` then turns the supplied
normalization witness for the specified longest-class lift into the literal
subset equality `associatedSubset actual J = J`. There is no maximality or
representation premise in this deduction.

`pointRankOneSelfTerm_subsingleton_of_other_class` works for a maximal `J` and
arbitrary inside-Levi cuspidal `σ`. At a minimal self representative other than
`1` and `(longestRep actual J)⁻¹`, the Coxeter classification contradicts
fullness of the source intersection. Then
`pointCuspidalGeometricTermVanishing_of_rootComparisons` proves that the actual
normalized geometric term has subsingleton carrier. The statement concerns
every lift and every supplied source/target decomposition witness. It does not
need self-association; that condition is needed for combining both possible
survivors at the same Levi.

`pointRankOneOtherProperTerm_subsingleton` additionally assumes the literal
subset equality. For `K ≠ univ` and `K ≠ J`, fullness would force either `K = J`
or `K = associatedSubset actual J = J`, so the same cuspidal-vanishing theorem
kills every term toward `K`. The target `K` need not itself be maximal.

`pointRankOneInverseLongestTermIso` is the actual isomorphism, for any lift `r`
of `(longestRep actual J)⁻¹`, from its self geometric term to
`(conjugationFunctor n⁻¹ _).obj σ`, using the exact lift `n` and normalization
witness `hself` supplied by the rank-one target. It uses
`geometricTermSameWeylClassIso` with reference lift `n⁻¹`. The full point
centralizer lies in every standard Levi by `centralizerPoints_le_levi` and the
explicit point-centralizer comparison. The quotient relation and `hn` give the
same Weyl class. The resulting representation acts by `x ↦ σ(n * x * n⁻¹)`.
This is an isomorphism for every lift, not equality of the elementwise
conjugation maps.

## Provenance and declaration dependencies

These are derived consequences of the published term interfaces and finite
Coxeter results, not new structural assertions taken from literature.
The finite proofs use `simple_injective`,
`intersectionSubset_eq_source_iff_mapsIntoSimple`,
`coatom_simpleSurvivor_classification` and elementary finite cardinalities.
The actual vanishing proofs use
`pointCuspidalGeometricTermVanishing_of_rootComparisons` from
[RationalCuspidalGeometricTerms](RationalCuspidalGeometricTerms.md). That theorem
uses `pointGeometricSourceJacquet_subsingleton_of_cuspidal`, the actual
`pointSourceIntersectionIdentities`,
`geometricSourceJacquetComparisonIso`,
`isCorollaryLeviCuspidal_iff_isLeviCuspidal` and
`geometricTerm_subsingleton_of_source_subsingleton`. Cuspidality supplies the
proper restricted Jacquet vanishing; induction and conjugation preserve the
zero carrier. The inverse-longest isomorphism uses the full-Levi term and
inner-conjugation comparisons documented in
[RationalGeometricLiftComparison](RationalGeometricLiftComparison.md).
Normalization-to-subset equality uses
[RankOneLongestLiftNormalization](RankOneLongestLiftNormalization.md) and
[RationalAssociatedLeviConjugation](RationalAssociatedLeviConjugation.md).

No proof of the geometric lemma, adjointness, a cuspidal-support theorem,
character independence or Langlands classification is invoked in these
proof bodies or in the documented dependency routes above. Imported modules
also contain separate representation-theoretic targets and conditional
assemblies; their presence supplies no instance of those targets. In
particular, no Grothendieck-class equation is used as object-level evidence.

## Remaining obligation

A finite filtration of the actual `r_K(i_J σ)`, with the actual normalized
geometric terms as grades, is still needed. For the self term its order must
put the identity piece above the inverse-longest piece to produce the
specified short exact sequence. Termwise vanishing by itself establishes
neither that filtration nor the ambient Jacquet vanishing. An empty label type
has no coatom source, so no nonemptiness premise is introduced.
