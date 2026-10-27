# Joint continuity for open normal-level actions

This internal construction refines the actual quotient-space actions in
[NormalLevelCover](NormalLevelCover.md) and their coefficient-kernel tower in
[CongruenceLevels](Coefficients/CongruenceLevels.md). Its provenance is the
quotient topology and Mathlib's continuous-action category. No additional
literature claim is made.

Let `G` be a topological group, `U` a subgroup, and `N` a normal subgroup of
`U`. For a group `Γ`, topological space `X` with a `Γ`-action, and homomorphism
`ι : Γ →* G`, the existing residual action on the actual double quotient
has the formula `[x,a] ↦ [x,a u⁻¹]`. These groups and the space have independent
universes. As before, continuity of the `Γ` action is not required.

`normalQuotientMk` bundles the actual map `U → U/N` as a continuous monoid
homomorphism for the subtype and quotient topologies. For `N ≤ P`,
`normalQuotientContinuousMap` bundles the published identity-induced map
`U/N → U/P`. Its continuity follows from the quotient-map criterion: its
composite with `U → U/N` is the continuous map `U → U/P`. This construction
requires no openness.

If `N` is open in `U`, Mathlib's quotient-topology theorem makes `U/N`
discrete. `normalQuotientAction_isContinuous` then proves joint continuity
of the residual action: a map from a product with a discrete first factor
is continuous if each slice is continuous, and each slice is already a
continuous endomorphism in the published action. No finiteness or topology
change is used. `normalQuotientContinuousAction` is the existing action
together with this proof in `ContAction TopCat (U/N)`.

`normalContinuousAction` certifies `normalLevelAction` using the continuity
proof obtained by restriction along the actual continuous quotient map.
Its underlying action is definitionally `normalLevelAction`.
Thus the original topological group `U` acts jointly
continuously as well. `normalContinuousCoverMap` lifts the existing
forgetful map to the continuous residual actions, using the continuous
quotient homomorphism. `normalContinuousLevelMap` presents that same map
as a morphism of continuous actions of the fixed group `U`; its
equivariance is the residual equivariance evaluated at the class of each
`u ∈ U`. Its identity and composition lemmas follow by extensionality from
the published normal-cover map laws. The maps and quotient-space topologies
are unchanged.

For a compact open `U`, a commutative coefficient ring `R`, an integral
representation `M` of `U`, an ideal `I`, and openness of its congruence
kernels, `congruenceContinuousLevelSpaces` assembles the spaces into a
functor `ℕᵒᵖ → ContAction TopCat U`. The action at exponent `n` is precisely
the existing inverse-right action, with its proved joint continuity.
Transition maps send `[x,a]` to `[x,a]`. The identity and composition laws
come from the actual normal-cover maps. This fixed-group presentation
complements the varying finite-quotient presentation; it does not replace
or change the existing congruence-group functor.

`compactCoefficientContinuousLevelSpaces` specializes this construction
to the actual stable compact adelic coefficient lattice, retaining the
explicit local orbit-continuity hypothesis `hρ` and nonzero rational
scalar `m`. Openness of every kernel is supplied by the published
`compactCoefficient_congruenceKernel` theorem. The coefficient algebra,
number field, and coefficient module share a universe, while `Γ` and `X`
have independent universes.

The shared [TopCatSelfForget](../CategoryTheory/TopCatSelfForget.md) module
supplies `Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget`,
the identity `HasForget₂` instance needed to apply Mathlib's continuous-action
category to `TopCat` itself. It is installed locally in this module.

Rational stabilizers remain in the double quotient. These constructions
assert no cofinality of the congruence kernels, freeness or faithfulness,
finite fibers, covering or torsor property, scheme realization, canonical
models, associated sheaf comparison, or cohomology.
