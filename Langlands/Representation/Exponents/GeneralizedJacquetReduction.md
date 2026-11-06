# The generalized Jacquet lemma follows from uniform compression stabilization

Author: Worker 1587. Module `Langlands.Representation.Exponents.GeneralizedJacquetReduction`, namespace `Langlands.Aubert.General.RationalPointFamily`.

`generalizedJacquetLemma_of_uniformCompressionStabilization` proves the implication from the exact published proposition `UniformCompressionStabilizationStatement.{u, v}` to the exact published proposition `GeneralizedJacquetLemmaStatement.{u, v}`, for arbitrary independent universe levels `u` and `v`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.9.1, printed pp.195–197 / PDF pp.201–203, especially the deduction following the Proposition on PDF p.203. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof introduces the exact field, connected reductive group scheme, rational-point topology, dynamic subgroups of the cocharacter, compact open subgroup, and M-central contracting element of the target. It applies the supplied uniform-stabilization proof to those same data. For the given smooth representation, its stationary-range conclusion supplies the premise of `Jacquet.fixedJacquetMap_surjective_of_stationaryRanges`. The normalizer proof is exactly `Dynamic.centralizer_le_normalizer_unipotent χ (Over.mk (𝟙 _))`, as in the published target.

The abstract helper uses compression-power intertwining, opposite contraction, factorization and compact averaging. It proves surjectivity by cancelling an invertible power of the Jacquet action after passing to stationary compression ranges. This avoids constructing the localization used by Renard. Neither kernel stationarity nor the complementary decomposition is needed for this surjectivity deduction.

The dynamic-parabolic hypotheses and centrality of the contracting element enter the call to the uniform-stabilization proposition. The latter is still an explicit premise of this reduction theorem. This module supplies no proof of uniform stabilization and does not itself prove the unconditional generalized Jacquet proposition. No admissibility, finite length, finite generation or finite-dimensional fixed-vector premise is introduced.
