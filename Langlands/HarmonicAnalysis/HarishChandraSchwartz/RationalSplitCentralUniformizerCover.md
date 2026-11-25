# The actual split-central chamber cover from the joint structural input

This internal auxiliary construction for Waldspurger's Corollary VIII.3.2 on
the actual compatible split-central quotient derives the split-central
quotient cover used in the cell-volume and height-series arguments from the
published proposition `JointSpecialCompactBasisExistenceStatement`.

For the actual maximal split-torus inclusion `i`, its standard cocharacter
`ν`, and an actual split-component inclusion `s`, the proposition
`RationalSplitCentralUniformizerCover i ν s` asserts that there are one compact
open subgroup `H` of `G(F)` and one compact subset `Y` such that every point
of the actual quotient
`LeftQuotient (rationalPoints.map s).range` belongs to an image

`q '' (H * {ϖ^y} * Y)`

for some actual cocharacter `y` of the maximal split torus. Each such `y`
has nonnegative simple-root pairings, and its actual uniformizer power lies
in `rationalCommonNormKernel G`, the published `G¹`. The proposition concerns
the sets in the quotient, and its compact open `H` is chosen independently
of the Xi-defining compact and the structural subgroup in the VIII.3 target.

`rationalSplitCentralUniformizerCover_of_jointSpecialCompactBasis` proves
this proposition assuming `JointSpecialCompactBasisExistenceStatement.{u}`.
It applies over any nonarchimedean local field in arbitrary universe `u`,
with an affine locally finite type connected reductive group, maximal split
torus, generic cocharacter and actual split component. The proof first uses
the published standard-cocharacter and relative-root-system theorems to construct
`NormKernelFundamentalCocharacters`. Its positive orthant has positive
simple-root diagonal pairings and zero other pairings; every orthant point
annihilates all ambient rational characters. Thus all its actual uniformizer
powers are dominant and lie in `G¹`, including when the simple-root set is
empty.

Apply the assumed joint existence statement at the fixed torus and generic
cocharacter. Its witnesses provide one geometric compact subgroup `H`, a
represented centralizer and compatible Cartan comparisons. Compactness and
openness of that same `H` come from its `SpecialCompactProperties`. Its
centralizer lattice conclusions supply a finite lattice transversal. The
published
`NormKernelFundamentalCocharacters.exists_finite_centralCartanFactorization`
then gives finite residual charts for the specified positive orthant, with
a final factor in the full abstract rational-point center. The factorization
uses the apartment and Cartan data of the joint witness.

Absorb the finite residual set and the final compact subgroup into a compact
right factor. Apply
`exists_rationalSplitCentralQuotient_cover_of_central_cover` to replace the
remaining full-central factor by its compact remainder modulo the actual
split-component point image. The resulting cells retain the same positive
orthant parameters and therefore the same `G¹` property. Their left factor
is the one compact open `H` already constructed. This proves the displayed
cover proposition.

The provenance is internal composition of these structural and algebraic
constructions. The use of the full joint hypothesis is in the choice of the
open compact and the Cartan witnesses for the factorization.
