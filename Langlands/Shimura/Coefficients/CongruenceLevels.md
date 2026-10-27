# Compact congruence levels and their equivariant quotient-space tower

This internal construction combines the actual double-quotient spaces in
`Langlands.Shimura.Levels`, residual actions in `NormalLevelCover`, coefficient
congruence groups in `FiniteQuotient`, and the constructed compact-level stable
lattice in `CompactCoefficient`. Its provenance is this assembly of published
and separately reviewed constructions; no additional literature claim is made.

For a topological group `G`, compact open level `U`, and an open subgroup `N`
of `U.subgroup`, `CompactOpenLevel.sublevel` constructs an actual compact open
subgroup of `G`. Its subgroup is `N.map U.subgroup.subtype`. The inclusion
of the open subset `U` is an open map, so this subgroup is open in `G`. Open
subgroups of a topological group are closed, and it is contained in the compact
set `U`; therefore it is compact. `sublevelInclusion` is its actual ambient
transporter arrow back to `U`. Relative normality is not needed for this step.

The general coefficient construction takes a commutative ring `R`, an integral
action `M` of `U.subgroup` on an `R`-module, an ideal `I`, and openness of every
actual `congruenceKernel I M n`. The ring, group, and module have independent
universes. `congruenceLevel` applies the preceding construction to each kernel.
`congruenceLevelMap` is the ambient inclusion from exponent `j` to exponent
`i` for `i ≤ j`, using the proved antitonicity of the congruence kernels.
`congruenceLevelTower` assembles these levels and arrows into a functor on
`ℕᵒᵖ`, including exponent zero.

For any homomorphism `ι : Γ →* G` and topological `Γ`-space `X`,
`congruenceLevelSpaces` is an `EquivariantDiagram` over the existing, unchanged
functor `torsionCongruenceGroups I M`. Its underlying space diagram is the
constructed compact-level tower followed by the actual `LevelSpace.tower`.
At exponent `n`, the group is exactly
`U.subgroup / congruenceKernel I M n`, acting by `[x,a] ↦ [x,a u⁻¹]`.
Transition maps forget level and send `[x,a]` to `[x,a]`. Equivariance follows
from `normalCoverMap`, with the quotient homomorphism induced by the identity
on `U.subgroup`. Thus the geometry and the already constructed coefficient
diagram use the same group functor and the same inverse-index convention.

`congruenceLevelProjection` is the natural transformation from this diagram to
the constant original `U`-level. Each component is surjective and invariant
under its residual quotient group. Naturality is proved by the projection
compatibility of normal-level forgetful maps.

The final section instantiates the construction with the actual rational
algebra-with-involution, algebraic representation, coefficient place, compact
adelic level, and orbit-saturated stable lattice from `CompactCoefficient`.
It retains that module's explicit hypothesis `hρ` of continuity of local
algebraic orbit maps. For a rational scalar `m ≠ 0`, the published
`compactCoefficient_congruenceKernel` supplies openness of every kernel.
`compactCoefficientCongruenceLevels` is the resulting actual ambient
compact-open level tower. `compactCoefficientCongruenceSpaces` is its actual
quotient-space diagram over the lattice's `rationalCongruenceGroups m`;
every group is finite by the same published theorem.
`compactCoefficientCongruenceProjection` specializes the natural base
projection. The algebra, number field, and algebraic coefficient module have a
common universe; `Γ` and `X` have independent universes.

These constructions do not assert that the kernels are cofinal among all
levels. They construct actions by continuous maps and equivariant surjective
forgetful maps; they do not assert joint continuity, freeness, faithfulness of
the geometric action, finite fibers, a covering or torsor property, canonical
models, scheme realization, descended coefficient sheaves, or a comparison
between cohomology theories. In particular, rational stabilizers are retained.
