# Profinite congruence groups and continuous level-limit actions

This file constructs a profinite group diagram from the actual coefficient
congruence quotients and its jointly continuous action on the actual inverse
limit of normal-level double quotients. It then specializes the construction to
the published compact lattice for an algebraic coefficient representation.
The specialization supplies the proved openness of every kernel; there is no
orbit-continuity hypothesis or chosen action on the limit.

## Provenance and inputs

This is an internal construction from
`Langlands.Shimura.Coefficients.AlgebraicCompactCoefficient`,
`Langlands.Shimura.NormalLevelContinuous`, the underlying coefficient-congruence
and normal-cover constructors, and
`Langlands.CategoryTheory.EquivariantDiagramLimit`. Mathlib supplies the actual
quotient-group topology, compactness and discreteness results, the category
`ProfiniteGrp`, and its explicit compatible-family limit. This file makes no
new attribution to a theorem of Harris or a geometric comparison.

The general input consists of a commutative ring `R : Type u`, a topological
group `G : Type v`, a compact open level `U`, an action
`M : Action (ModuleCat.{w} R) U.subgroup`, an ideal `I`, and
`hN : ∀ n, IsOpen (congruenceKernel I M n : Set U.subgroup)`.
Write `Nₙ` for this normal kernel of the actual action on the ideal-power
coefficient quotient. Neither the ring nor the module needs a topology,
finiteness hypothesis or continuity hypothesis in this general constructor;
the required openness is explicit. Compactness of `U.subgroup` follows from
the existing compactness field of `U`.

For the space action the additional inputs are a group `Γ : Type z`, a space
`X : Type t` with a `Γ` action, and a homomorphism `ι : Γ →* G`. The output
spaces lie in `TopCat.{max v t}`. No continuity of the `Γ` action, separation,
compactness or nonemptiness of `X` is required.

## The actual profinite quotient diagram

`congruenceQuotient_finite` proves that `U.subgroup ⧸ Nₙ` is finite. Its
topology is the existing quotient topology: the image of compact `U.subgroup`
is compact, and `QuotientGroup.discreteTopology (hN n)` certifies that this
topology is discrete. A compact discrete space is finite. In particular the
construction does not replace the quotient topology by a chosen finite-space
topology.

`congruenceProfiniteGroup` bundles this same topological quotient in
`ProfiniteGrp.{v}`. Discreteness provides total disconnectedness.
`congruenceProfiniteTransition`, for `j ≤ i`, bundles the existing continuous
homomorphism

`U/Nᵢ → U/Nⱼ`, `[g] ↦ [g]`.

The inclusion `Nᵢ ≤ Nⱼ` is the proved antitonicity of the coefficient
congruence kernels. These objects and maps define
`congruenceProfiniteGroups : ℕᵒᵖ ⥤ ProfiniteGrp.{v}`. Its identity and
composition obligations use the published congruence-transition laws
pointwise. The maps are surjective by the existing quotient-transition
surjectivity theorem. The `_map_mk` lemma records their representative formula.
`congruenceProfiniteGroups_forget` states that forgetting topology recovers
exactly `torsionCongruenceGroups I M`, including its transition maps.

## Compatible groups and the original compact level

`congruenceGroupLimit` is Mathlib's explicit `ProfiniteGrp.limit` of this
diagram. Its elements are compatible families `g = (gₙ)` in the product of the
actual quotient groups; its topology is the inherited product-subtype
topology. `congruenceGroupLimitProjection` is the actual continuous homomorphism
from the limit cone, with value `gₙ`.

`congruenceGroupLimitMap` constructs the continuous homomorphism

`U.subgroup → limₙ U/Nₙ`, `g ↦ ([g])ₙ`.

Compatibility and the group laws follow from the actual quotient maps.
Continuity follows by product and subtype continuity from continuity of each
quotient map. The `_apply` and `_Projection_comp_map` formulas identify its
coordinates and their composites with the projections. Its kernel theorem is
the equality

`ker(congruenceGroupLimitMap) = ⋂ₙ Nₙ`.

The proof evaluates a limit equality at each coordinate and uses
`QuotientGroup.eq_one_iff`; conversely those coordinate equalities give equality
in the compatible-family subtype. No injectivity, surjectivity, density or
isomorphism assertion about this original-level map is made.

## Continuous actions on the actual level-space limit

Let `F = congruenceLevelSpaces U I M hN ι`. Its underlying spaces are the
published double quotients at the ambient subgroups `Nₙ.map U.subgroup.subtype`,
and its varying residual acting groups are `U/Nₙ`. These are exactly the
groups underlying `congruenceProfiniteGroups`. The relative subgroup `Nₙ`
is normal in `U.subgroup`; its ambient image need not be normal in `G`.

`congruenceLevelLimitAction` applies the published profinite-diagram action
engine to `F`. The required joint continuity of every residual action is
proved by `LevelSpace.normalQuotientAction_isContinuous`, using openness of
`Nₙ`. The underlying space is exactly the point of `TopCat.limitCone F.obj`,
as recorded by `_obj`: it is the subtype of compatible space coordinates in
the product with its inherited topology. The action formula is

`(g · x)ₙ = F.ρ n gₙ (xₙ)`.

The generic engine supplies preservation of compatibility, the action laws
and joint continuity. `congruenceLevelLimitProjection` constructs the
continuous equivariant projection `x ↦ xₙ`. Its target is the existing
continuous action on the level-`n` double quotient restricted along the
actual group-limit projection.

`congruenceOriginalLevelLimitAction` restricts this limit action along the
constructed continuous `congruenceGroupLimitMap`. Its `_apply` lemma identifies
each coordinate with the original `LevelSpace.normalLevelAction`. This is the
published left action by inverse-right translation:
`g · [x,a] = [x,a*g⁻¹]`. Rational stabilizers in the double quotient are
retained; no freeness assumption enters the construction.

## Algebraic compact coefficient specialization

Here `A`, the number field `L` and the finite-dimensional coefficient module
`W` lie in `Type u`. The other inputs are the actual involution `σ`, its
algebraic coefficient representation `ρ`, finite places `p` of `ℚ` and `l`
of `L` with the existing `LiesOver` instance, and an actual compact open
`U : CompactOpenLevel σ.FiniteAdelicPoints`. Fix a natural scalar `m` with
`hm : m ≠ 0`. All exponents, including zero, are retained.

Set `Λ = algebraicCompactCoefficientLattice ρ p l U` and
`I = coefficientScalarIdeal l m`. This is the published orbit-span stable
lattice at one coefficient completion. Its continuity and the openness of its
congruence kernels have already been derived from algebraic naturality.
Every new specialization uses precisely `Λ.action`, `I`, and the openness
proof `(algebraicCompactCoefficient_congruenceKernel ρ p l U m hm n).1`.

`algebraicCompactCongruenceProfiniteGroups` is the constructed profinite
diagram. Its forgetful identity identifies it with
`Λ.rationalCongruenceGroups m`, the group diagram acting on the existing
algebraic compact coefficients. The group limit, continuous original-`U` map,
continuous group projections, coordinate formulas and kernel-intersection
theorem are the corresponding `algebraicCompactCongruenceGroupLimit*`
declarations.

For `Γ : Type z` and `X : Type t` as above,
`algebraicCompactCongruenceLimitAction` acts in `TopCat.{max u t}` on the
actual compatible-family space of `algebraicCompactCongruenceSpaces`.
Its `_obj`, `_apply` and `algebraicCompactCongruenceLimitProjection`
declarations give the same underlying-space, action and projection
identifications as in the general construction.
`algebraicCompactOriginalLevelLimitAction` is restriction along the
constructed original-level map; its coordinate lemma recovers the actual
inverse-right normal-level action.

These constructions supply a topological group and its actual level-limit
action. They assert no cofinality among adelic levels, geometric covering or
torsor property, finite geometric fibers, identification with a scheme or
canonical model, sheaf descent, or cohomological comparison. Those conclusions
remain separate obligations in the broader Harris specialization.
