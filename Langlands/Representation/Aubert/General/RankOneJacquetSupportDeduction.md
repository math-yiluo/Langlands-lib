# Fixed-Levi Jacquet nonvanishing from associated support detection

Author: Worker 64.

This internal conditional construction identifies the detected subset with the
required subset before applying the published rank-one assembly. It has
independent index, ambient-group and carrier parameters `uI`, `uG`, `uV`.
The group is locally compact and nonarchimedean; the finite index type may be
empty. The actual complex smooth representations have carrier universe
`max uG uV`.

`HasTwoConstituents.isSubquotient` records that each endpoint of an actual
length-two constituent sequence is an actual subquotient of its middle. An
injective endpoint map gives a subrepresentation, and a surjective endpoint map
gives a quotient. Both orientations in `HasTwoConstituents` are handled.

`jacquet_nontrivial_of_support_detection` assumes:

- the published irreducible support-detection target for the supplied standard
  subgroup families and association relation;
- the compact-limit property of every unipotent subgroup, used for exactness;
- a representation `E` in the support category of a subset `I`;
- an irreducible actual subquotient `π` of `E`;
- properness of every subset associated to `I`;
- zero actual middle Jacquet modules `r_K(E)` for every proper `K ≠ I`.

Closure under subquotients puts `π` in the same support category. The supplied
detector gives some `K`, a representative `n`, the association and actual Levi
conjugation conditions, and nontrivial `r_K(π)`. If `K ≠ I`, properness makes
`r_K(E)` zero by hypothesis. The published
`jacquet_subsingleton_of_isSubquotient` then makes `r_K(π)` zero, a
contradiction. Thus `K = I`, and substitution gives the nontriviality of the
literal Jacquet object at `I`. No comparison of Jacquet modules at different
Levis is needed.

`jacquet_nontrivial_cuspidalInduction_subquotient_of_support_detection`
specializes this argument to `E = i_I(σ)`, with irreducible Levi-cuspidal `σ`.
It uses the supplied identity association and the published
`isInSupportCategory_cuspidalInduction` to obtain support-category membership.
Both this identity association and associate properness remain explicit
premises in this generic module.

`rankOneJacquetConstituentsOfSupportDetection` applies that result to both
irreducible endpoints of the supplied actual constituent sequence. It then
calls `rankOneJacquetConstituentsOfExactData` with the derived nontriviality
witnesses, the supplied actual geometric middle sequence and the supplied
other-proper middle vanishings. The result is an ordered pair of actual
finite-length constituents with `HasTwoConstituents` and the existing
`RankOneJacquetPattern`. The supplied normalizer lift and self-normalization
witness are retained literally; the inverse-conjugation endpoint is the one
defined by that pattern.

The direct dependencies are the actual subquotient conversion lemmas
`IsSubrepresentation.isSubquotient` and `IsQuotient.isSubquotient`, support
closure and induction membership in `SupportCategory`, actual Jacquet
zero propagation in `SupportCategoryReductions`, and actual endpoint assembly
in `RankOneJacquetAssembly`. The subquotient conversion lemmas live in
`Classification/SupercuspidalSupport`, but their proofs only construct an
injective/surjective presentation of the actual invariant-subspace quotient.
They use no classification or support-existence theorem. The support closure
uses the proved elementary subquotient-transitivity result. Jacquet zero
propagation uses `jacquetFunctor_map_isShortExact`, which applies
`characterLocalizationExactness` at the trivial character. The assembly's
composition-factor and conjugation dependencies are documented in its
[paired explanation](RankOneJacquetAssembly.md).

This unit supplies no instance of the irreducible support detector, no
geometric middle sequence, no other-proper middle vanishing theorem and no
existence theorem for finite-length constituents. It uses no adjointness,
character-independence or Langlands-classification theorem to fill these
premises. The support-theoretic assertion is explicitly assumed, and geometric
data are explicitly supplied. In particular this conditional construction
does not prove `RationalRankOneJacquetModulesStatement`.
