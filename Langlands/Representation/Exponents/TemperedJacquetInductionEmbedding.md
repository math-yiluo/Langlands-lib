# Induction embeddings from a tempered unitary Jacquet part

This derived supporting unit implements the Frobenius reciprocity step in
Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
VII.2.6, first proof paragraph, printed p.231 / PDF p.237. It combines the
actual induction map of `TemperedUnitaryJacquetEmbedding` with the
pointwise consequences of temperedness in `TemperedJacquetStructure`.

The field universe `u` and representation carrier universe `v` are independent.
The field is a Hausdorff nonarchimedean local field. The ambient rational
points have their canonical topology and the supplied local compactness and
nonarchimedean group instances. The actual parabolic, rational Levi, matching
geometric radical, multiplication isomorphism and split component are retained.

`temperedUnitaryJacquetQuotientInductionMap` sends the ambient representation
into the published normalized `leviInductionFunctor` of the selected actual
irreducible unitary Jacquet quotient. It applies
`unitaryJacquetQuotientInductionMap`, supplying radical unimodularity and
complementarity from temperedness. Its injectivity theorem applies the
published injectivity result when the source is irreducible. These two
constructions expose an affine Levi instance and use its canonical topology.

`IsNormalizedExponentTempered.exists_irreducible_induction_embedding` derives
the affine Levi structure internally and uses the published quotient selector
and embedding result. Besides temperedness and irreducibility, this corollary
still assumes compactness of the literal left quotient by the parabolic point
image and nontriviality of the actual unitary Jacquet summand. Its conclusion
is an actual irreducible Levi representation and an injective intertwiner
into its normalized induction, using `leviPointTopology`.

This unit asserts no square-integrability of the selected quotient. The
minimality argument, quotient temperedness, square-integrability criterion,
uniqueness and unitarizability remain separate. In particular it does not
prove the unconditional VII.2.6 propositions.
