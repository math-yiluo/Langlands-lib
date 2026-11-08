# The represented completion theorem from global structural inputs

Author: Worker 1775. The derived internal proposition
`LeviCompletionStructureStatement : Prop` states that parabolic dynamics and
uniform compression stabilization imply the exact published
`LeviCompletionOppositeJacquetStatement`. The accompanying theorem
`leviCompletionOppositeJacquet_of_structure` implements this implication
with two explicit premises:
`GroupScheme.ParabolicDynamicStatement` and
`RationalPointFamily.UniformCompressionStabilizationStatement`.
Neither premise is proved here, so this is not an unconditional proof of
VI.9.7. Opposite dynamic-parabolic uniqueness is imported as the proved theorem
`GroupScheme.oppositeDynamicParabolicUniqueness`.

The underlying source is Renard 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
VI.9.7, printed pp.205–206 / PDF pp.211–212, and VI.9.1, printed
pp.195–198 / PDF pp.201–204. The reduction follows the source's stable-image
description of the completion, using the previously constructed conditional
completion comparison. Its provenance is internal assembly: it establishes
the precise implication between the existing Library statements without
asserting their remaining inputs.

All field and carrier universes and every quantifier of the published
conclusion are retained. In particular, the field is any nonarchimedean local
field with the specified valuation and Hausdorff topology, the ambient
group scheme is connected reductive, and its rational points have the
canonical topology with the statement's local compactness and
nonarchimedean-group instances. The parabolic triples are actual rational
morphisms with their geometric unipotent radicals and multiplication
isomorphisms. The given Levi morphisms have the same composite into the
ambient group, and the two parabolic point images intersect in that Levi
image. Representations in the conclusion have arbitrary carrier universe
`v`; no admissibility or finiteness assumption is added.

The proof first uses parabolic dynamics to realize the quotient parabolic
`Pbar` and its given rational Levi by a cocharacter `χ`. The actual radical
image is then `N(χ)(k)`. The proved opposite uniqueness theorem, applied to
the same-Levi and rational-point intersection hypotheses with the two
parabolics exchanged, identifies the fixed radical image with
`N(χ⁻¹)(k)`. The dynamic contraction theorem supplies a single Levi-central
element `g` and a neighborhood-cofinal opposite Iwahori contraction basis
for these literal subgroup images, before any representation is chosen.

For each basis index `K`, uniform compression stabilization gives a
stationary image and a Fitting splitting for every smooth representation.
The stationary image is obtained by taking the exponent furnished by the
statement. The genuine stable-image Jacquet map is bijective by
`Jacquet.stableImageJacquetMap_bijective_of_splits`. These supply exactly the
remaining inputs of `leviCompletionComparisonEquiv`; its already proved
compact covering, Levi-point transport and normalization comparisons are
used unchanged.

This constructs one family of linear equivalences for all smooth
representations. For the characterization, the contracting element at the
test index may differ from the element used to construct the family. Only
the factorization field of the test `IsIwahoriContraction` is used in
`leviCompletionComparisonEquiv_apply_of_factor`; equality of the Levi
embeddings identifies its middle factor with the construction's Levi
image. The resulting formula is the exact `Jacquet.Localization.mk … 1`
formula in the published statement, at every actual Levi compact open
index with the required ambient image. Naturality follows from
`leviCompletionComparisonEquiv_natural` for the genuine normalized
`leviJacquetFunctor` and the supplied equality of ambient components.

The normalization, Levi topology and component formulas are those of the
published statement. The first parabolic's multiplication isomorphism and
the test element's centrality are available hypotheses but are not needed
by this final assembly. The two retained global propositions remain the
separately owned structural and VI.9.1 obligations.
