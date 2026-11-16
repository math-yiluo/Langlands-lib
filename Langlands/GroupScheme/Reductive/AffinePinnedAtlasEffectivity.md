# Effective corrected pinned atlas descent and quasi-split torus data

Let `G` be a reductive group scheme over an arbitrary scheme `S` in any
universe. Let `A` be an affine pinned atlas of `G`, and let `P` be a supplied
`RelativePinnedComparison`. This internal construction applies effective
étale descent to the actual corrected atlas datum `A.datum P`.

The atlas projection is étale and surjective. The group on the atlas is the
actual pullback of `G`, hence is reductive and has affine structure morphism.
`AffinePinnedAtlas.solution` applies `Datum.etaleSolution` to this datum and
constructs an actual solution. In particular, no descent solution is required
as an input. The instance `solution_isAffineHom` retains the affineness
guarantee of that constructor. No affineness assumption on `S` and no
quasi-compactness assumption on the atlas projection are used.

`quasiSplitTorusData` applies the actual-solution geometry construction
`relativeQuasiSplitTorusData` to this solution. It supplies reductivity, an
actual relative Borel subgroup, and a closed fibrewise maximal relative torus
whose range lies in that Borel. Its existing `quasiSplit` consequence proves
`solution_isRelativeQuasiSplit`.

All assertions are compositions of the corrected pinned atlas construction,
arbitrary-base affine-group étale effectivity and the actual-solution dynamic
subgroup geometry. This module makes no new literature assertion. The
relative pinned comparison remains an explicit input. Its existence and the
inner-discrepancy property are separate obligations for the unconditional
quasi-split inner-form theorem.
