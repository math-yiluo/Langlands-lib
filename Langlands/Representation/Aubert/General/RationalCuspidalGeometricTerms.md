# Vanishing of actual geometric terms on rational cuspidal data

Worker 167. This internal unit proves vanishing of actual source Jacquet
modules and actual geometric terms when the intrinsic source intersection
is proper. Its representation-theoretic input is the original Levi
cuspidality condition. It adds no geometric-lemma assumption or
finite-length preservation hypothesis.

For a topological group `G` in universe `uG`, a root-label type in universe
`uI`, and subgroup families `P`, `M`, `U`, the theorem
`geometricSourceJacquet_subsingleton_of_cuspidal` takes a representation
`σ : SmoothRep.{0, uG, uV} ℂ (M J)` with `IsLeviCuspidal`.
The restricted standard parabolics of `M J` have the supplied
semidirect decompositions. A finite subset `K` of the labels in `J` is
proper, meaning `K ≠ Finset.univ`. Assume the actual source-intersection
Levi equals `M (leviIndex J K)` and its radical, regarded as a subgroup
of `M J`, equals the corresponding restricted standard radical.
For every source-decomposition witness, the carrier of the actual source
Jacquet representation is then a subsingleton.

The implemented proof uses `geometricSourceJacquetComparisonIso` from the
published source-comparison module. Its target is the restricted
standard Jacquet module killed by `IsLeviCuspidal` at `⟨K, hK⟩`.
Injectivity of the underlying linear equivalence transfers the
subsingleton property back to the actual source module. The inclusion
of the intersection Levi into `M J` follows directly from its definition
as an intersection.

`geometricTerm_subsingleton_of_source_subsingleton` transfers vanishing
from the actual source Jacquet module to the entire actual term. It
works with the universe saturation already used by
`geometricTermFunctor`: the input has carrier universe `max uG uV`.
Conjugation and restriction keep the same carrier. The final normalized
induction is represented by a space of smooth functions with
subsingleton values, so that space is a subsingleton. A private lemma
spells out this last step. No assertion that induction preserves
finite length is needed.

In `RationalPointFamily`, the proposition-valued definition
`PointCuspidalGeometricTermVanishing.{u, v}` retains an arbitrary field
and affine group scheme in universe `u`, a monomorphic torus inclusion,
the literal simple-root type, its finite instance, and the actual
Coxeter system. The rational-point group has the project point topology
and is locally compact and nonarchimedean. The standard Levi and
unipotent subgroups are closed; the original connected-reductive,
maximal-split, generic-cocharacter and standard-Levi-intersection inputs
supply the restricted decompositions.

The definition quantifies over every source subset `J`, target subset
`I`, `(I,J)`-minimal actual Weyl class `w`, every normalizer lift `n`
of that class, and every actual source and target decomposition witness.
For every representation
`σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)`,
it retains exactly
`IsCorollaryLeviCuspidal.{u, u, max (u + 1) v}`. If
`intersectionSubset actual I J w ≠ J`, the actual geometric term on
`σ` has a subsingleton carrier. There is no maximality or
non-self-association restriction in this vanishing statement.

`pointGeometricSourceJacquet_subsingleton_of_cuspidal` proves the
source-module version from the point-normalizer and point-centralizer
comparisons, `RootLengthComparison`,
`PositiveSimpleReflectionComparison`, and
`StandardCocharacterStatement`. Set
`K := intersectionLeviIndex actual I J w`.
The published `leviIndex_intersectionLeviIndex` identifies its labels
with the intrinsic intersection, and minimality gives
`intersectionSubset_eq_simpleImage_inter`. Thus its standard labels
are `simpleImage actual w⁻¹ I ∩ J`. Properness of the intrinsic
intersection implies `K ≠ Finset.univ`. The published theorem
`pointSourceIntersectionIdentities`, applied to the supplied lift,
identifies the actual source Levi and radical with these restricted
standard subgroups. Finally
`isCorollaryLeviCuspidal_iff_isLeviCuspidal` converts the original
cuspidality condition and the generic source theorem applies.

`pointCuspidalGeometricTermVanishing_of_rootComparisons` proves the
named proposition by composing this rational source theorem with the
generic whole-term theorem. Both rational theorems retain the original
root comparisons; no new source-intersection premise is imposed on
their consumers.

The provenance is internal: all geometric identities and comparison
isomorphisms used here are imported published results, and the new
deduction uses only cuspidality, equality of the actual subgroups,
injectivity of an isomorphism, and the definition of induction.
The paired Lean file does not construct a geometric-lemma filtration,
identify a surviving term with the inducing representation, or prove
`RationalRankOneSelfAssociationStatement`.
