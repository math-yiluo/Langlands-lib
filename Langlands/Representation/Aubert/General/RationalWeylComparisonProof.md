# Scheme and point-image Weyl comparisons over local fields

Author: Worker 1344.

`Langlands.Aubert.General.RationalPointFamily.rationalWeylComparison` proves
the exact published `RationalWeylComparisonStatement.{u}`. It identifies
`GroupScheme.normalizerPoints i` and `GroupScheme.centralizerPoints i`
with the abstract normalizer and full centralizer of the actual rational
torus image `torusPoints i`.

The proof is an internal specialization of the published theorem
`GroupScheme.normalizerPointsInfiniteField`. The maximal split torus
hypothesis supplies `hi.isSplitSubtorus`. To prove the field is infinite,
`Valuation.IsNontrivial.exists_one_lt` supplies an element whose valuation
is greater than one. The powers of that valuation strictly increase by
`pow_right_strictMono₀`; applying the valuation to an equality of powers
proves that the powers of the field element form an injection from the
natural numbers. `Infinite.of_injective` supplies the required instance.
The local-field predicate supplies the nontrivial valuation used here.
The torus image and abstract subgroup
normalizer and centralizer in the target are definitionally the same as
those in the infinite-field theorem. No quotient identification,
relabeling of points, or replacement of the centralizer by the torus is
used.

The entire unapplied proposition is proved at arbitrary universe `u`.
Its original field, valuation, topology, connected reductive group and
maximal split torus binders are retained. No characteristic, ambient
splitness, quasisplitness or positive-rank condition is added, and the
empty torus is included.

The transitive mathematical input is the split-torus rational-point
detection in `GroupScheme.IsSplitTorus.exists_factor_of_kpoints` and
`GroupScheme.IsSplitTorus.hom_ext_kpoints`, used by
`normalizerPointsInfiniteField`. Its paired Markdown explains the
regular-function detection and all-test factorization argument.
This specialization uses no representation-theoretic theorem, Langlands
classification, character independence, geometric lemma, adjointness or
cuspidal-support theorem. It supplies one prerequisite for the rational
Corollary 1.10(b) assembly and does not assert that corollary.
