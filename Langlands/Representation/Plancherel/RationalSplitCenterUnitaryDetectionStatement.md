# Conditional unitary detection by the actual split-center point image

Author: Worker 200.

## Provenance and status

`ConditionalRationalSplitCenterUnitaryDetectionStatement` is an internal
consumer-adapter target for the published
`RationalSmoothCharacterModulus`, `RationalNormKernelCentralImage` and
`TemperedTwistIntegrability` interfaces. It defines a proposition and
does not prove it. It introduces no new original-source assertion.

The target places the existing generic `IsUnitaryDetecting` predicate
on the image of the actual rational-point map of a supplied split
component. Its purpose is to expose the remaining premises needed to
use that generic predicate in the rational-point setting.

## Actual objects and exact conclusion

The proposition universally quantifies a nonarchimedean local field
`F : Type u`, a connected reductive group scheme `M` over `F`, a
commutative group scheme `T` and a morphism `s : T.toGrp ⟶ M`.
The supplied proof `IsSplitComponent s` makes this a split component
of the actual center. Field characteristic is arbitrary; the ambient
connected reductive group need not be split or quasisplit.

`M(F)` carries the canonical `rationalPointTopology F M.X`, using
the affine structure supplied by connected reductivity. The subgroup
in the conclusion is exactly `(GroupScheme.rationalPoints.map s).range`.
It is not a freely supplied abstract central subgroup.

For this subgroup `A`, `IsUnitaryDetecting A` means:
for every homomorphism `θ : M(F) →* ℂˣ` whose kernel is open,
if `‖θ(a)‖ = 1` for every `a : A`, then `‖θ(g)‖ = 1`
for every `g : M(F)`. Smoothness is the displayed open-kernel
condition; continuity of `θ` is not a separate premise.

## Retained premises

In addition to `IsSplitComponent s`, the target retains:

1. Injectivity of the actual rational-character restriction
   `GroupScheme.characterRestrict s`.
2. `CentralNormKernelCompactness M hM`: compactness of the full
   scheme-center intersection with `rationalCommonNormKernel M`
   in the canonical rational-point topology.
3. `CentralDerivedNormKernelCocompactness M hM`: compactness of
   the actual norm kernel modulo the subgroup generated there
   by its scheme-central points and the supplied scheme-derived
   point subgroup, with the inherited and quotient topologies.
4. `DerivedSmoothRealAnnihilation M hM`: every real additive
   homomorphism from `M(F)` with open kernel kills the actual
   scheme-derived point subgroup.

The scheme-derived point subgroup is not identified with the
abstract commutator subgroup. None of these four premises is
discharged by this statement pair, hidden in the choice of topology,
or declared a permitted external structural input for completion
of the standing program.

## Derivation to be proved

The existing
`norm_eq_one_on_rationalCommonNormKernel_of_structure` yields
norm-one values on the actual common norm kernel from the three
local-point premises.

The existing `finite_rationalValuationQuotient_of_injective` yields
finiteness of the exact quotient
`rationalDiscreteValuationImage M / A.map (rationalValuationImageProjection M)`
from connected reductivity, split-component structure and the
retained character-restriction injectivity. The published identity
`rationalValuationImageProjection_ker` identifies the kernel of
that same projection with the actual common norm kernel.

These are precisely the hypotheses of the published generic
`isUnitaryDetecting_of_norm_eq_one_on_ker`. Its power argument
uses the finite quotient to put a positive power of any point
in `A` times the kernel and concludes norm-one values everywhere.
A focused proof must instantiate these interfaces; this description
explains the target's provenance and is not independent proof evidence.

The target needs no choice of Haar measure or representation.
It states no temperedness, rapid coefficient decay, integrability,
spectral finiteness, or Plancherel conclusion. Those consumer
obligations and the four retained premises remain separate.
