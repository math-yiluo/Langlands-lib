# Self-twist stabilizers and the topology of intertwining regions

## Scope and provenance

This module is a derived construction over the published actual-twist-class
and character-region interfaces. It defines the self-twist stabilizer and proves
its orbit and topology laws, then proves openness of the full-root regions used
in `ConditionalParabolicIntertwiningStatement`. The arguments are elementary
consequences of existing Library and Mathlib results; they do not rely on a new
external representation-theoretic or analytic assertion.

This unit proves no radical-unimodularity, squared-modulus, convergence or
rationality assertion. In particular it does not prove
`ConditionalParabolicIntertwiningStatement`. Its cone results apply to every
real threshold, so they can be used at the threshold ultimately supplied by the
analytic proof. Nonemptiness is already a separate Library result and is not
reproved here. The target module and all its imports remain unchanged.

## The stabilizer and the actual orbit

Let `L` be a nonarchimedean topological group, let `ν` be any indexed family of
positive-real-valued norm characters, and let `π` be any smooth complex
representation of `L`. The group and representation carriers and index type
have independent universes. No admissibility, finite length, nonzero-carrier,
or finite-stabilizer hypothesis is required.

`smoothRepUnramifiedTwistStabilizer ν π` is the subgroup of the existing continuous
unramified-character group consisting of characters `χ` for which the actual
twist of `π` is isomorphic to `π`. It is defined by equality in
`SmoothRep.IsoClass`, not by a selected representative. The subgroup laws follow
from `SmoothRep.IsoClass.twist_one` and `twist_twist`. Applying an inverse twist
also proves `unramifiedTwistClass_eq_iff`: the twists by `χ` and `ψ` have the same
class exactly when `χ⁻¹ * ψ` belongs to this subgroup.

For every character set `Ω`,
`unramifiedTwistOrbitSaturation_eq_mul` identifies its full actual-class
saturation with the pointwise product of `Ω` and the stabilizer. The proof uses
the fiber criterion in both directions. `IsOpen.mul_right` therefore shows that
the saturation of an open set is open, even when the stabilizer is infinite or
is the entire character group.

The actual orbit already carries the topology coinduced by
`unramifiedTwistOrbitMap`. An orbit image is open precisely when its inverse
image is open in the character space. Applying the saturation result proves
`isOpenMap_unramifiedTwistOrbitMap` and
`isOpen_unramifiedTwistOrbitRegion`.

## Scalar continuity of the normalized real part

`SplitTorus.continuous_normalizedRealPart_apply` takes a split torus `A` over a
nonarchimedean local field, a family `f` of complex-unit-valued characters of
its rational points, and continuity of each evaluation of that family. For
every real linear functional `ℓ` on `RealTorusSpace.Vstar A`, it proves
continuity of `x ↦ ℓ (SplitTorus.normalizedRealPart hA (f x))`. It does not
introduce a topology on that tensor space.

The perfect character-cocharacter pairing
`RealTorusSpace.isPerfPair_of_isSplitTorus` represents `ℓ` by a real
cocharacter tensor. `SplitTorus.pair_normalizedRealPart` reduces the assertion
to continuity of `extendLatticeLog (sectionLog (f x))` at that tensor. Tensor
induction reduces it to sums and scalar multiples of normalized logarithms of
norms of character values at `CocharacterUniformizer.latticeSection` points.
These values are units and hence nonzero, so `Continuous.log` applies to their
norms. The real normalizing divisor is fixed. The tensor-addition step uses
linearity and addition of continuous functions.

## Full-root cone openness and actual-point transport

`isOpen_canonicalUnramifiedIntertwiningRegion` rewrites the canonical region as
the intersection, over all `intertwiningRelativeRoots i U Uop'`, of its strict
root-threshold inequalities. Each inequality is open by the scalar-continuity
lemma: the scalar functional is evaluation of the supplied real bilinear form
at the root tensor. Character evaluation is continuous for the existing
topology by `continuous_eval_const`. The root set is finite by
`finite_intertwiningRelativeRoots`, and `Set.Finite.isOpen_biInter` finishes the
proof. There is no positivity or nondegeneracy assumption on the bilinear form,
and no nonempty-root assumption. Empty root sets give the whole character
space.

`isOpen_parabolicUnramifiedIntertwiningRegion` specializes that result to the
actual supplied radical images and compatible parabolic presentation.
`isOpen_parabolicPointUnramifiedIntertwiningRegion` then takes the continuous
inverse image through `parabolicLeviUnramifiedCharactersHomeomorph`.
Consequently it uses the literal ambient Levi point subgroup, its inherited
canonical rational-point topology, and the full indexed rational-character
norm family already specified by the target.

Finally `isOpen_parabolicPointUnramifiedTwistOrbitRegion` applies the generic
open-image theorem to every smooth representation of that literal Levi point
subgroup. It requires the same inherited nonarchimedean group structure used
in the target. These results preserve arbitrary characteristic, the actual
root intersection, rank zero, and the representation carrier universe.

## Dependencies and validation

The module imports
`Langlands.Representation.Plancherel.ParabolicIntertwiningStatement` for the
published orbit and actual-region interfaces and
`Mathlib.Topology.Algebra.Group.Pointwise` for openness of pointwise products.
The substantive declaration dependencies and proof routes are named above.
Lean compilation of the module succeeds with no errors or warnings. This is a
development check; independent semantic review and publication are still
required.
