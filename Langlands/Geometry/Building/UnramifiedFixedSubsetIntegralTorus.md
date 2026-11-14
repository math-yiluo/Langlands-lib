# Integral split tori from a subset fixed by unramified units

This module constructs an actual integral split torus in a supplied integral
model. It applies to an arbitrary set on which the unramified rational points
act, including a set of building points that has not yet been placed in a common
apartment.

## Inputs and result

Let `F : Type u` be a nonarchimedean local field, in either characteristic, and
write `K = inertiaFixedField F`. The valuation is the canonical integer-valued
`MaximalUnramified.valuation F`. Let `iS : S.toGrp ⟶ G` be a split closed
subtorus, and let `M : IntegralModel 𝒪[F] F G` be supplied. Smoothness and
reductivity are not needed for this construction.

The other inputs are a type `Y : Type v` with an action of `G_K(K)`, a subset
`Z : Set Y`, and these two hypotheses:

1. Every point of `Z` satisfies `IsFixedByUnramifiedTorusUnits F iS`.
2. The intersection of the ambient character-valuation kernel with the
   pointwise fixer `fixingSubgroup G_K(K) Z` is contained in
   `M.baseChangeUnramified.integralPoints`.

The second hypothesis is an inclusion into the integral-point group. Equality
with that group, existence of a model, Galois fixation, a metric, boundedness of
`Z`, and a common apartment are not asserted or required.

`integralSplitTorusOfUnitFixedSubset` chooses an
`IntegralSplitTorusData M iS`. Thus its output consists of an actual commutative
group scheme over `𝒪[F]`, a proof that it is split, an integral inclusion into
`M.group`, an isomorphism of its generic fibre with `S`, and the commuting
generic inclusion square. The theorem
`integralSplitTorusOfUnitFixedSubset_isClosedSubgroup` proves that the integral
inclusion is closed. No special-fibre maximality is asserted.

## Implemented proof

`map_characterValuationKernel_le_oneFixer_of_unitFixedSubset` first handles an
arbitrary source group homomorphism `i : H ⟶ G`. The published
`IntegerValuation.map_mem_characterValuationKernel` puts the image of a source
kernel point into the ambient character kernel. The definition
`IsFixedByUnramifiedTorusUnits` puts the same image in the pointwise fixer of
`Z`. This proves the requisite subgroup inclusion without using an apartment.

The existence theorem composes that inclusion with hypothesis 2 and applies
the published
`IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange`
to `M`, the maximal-unramified integer ring, and `K`. Its ancillary inputs are
the published
`SpecialTorusIntegralModel.infinite_residueField_fixedFieldIntegers`,
`SpecialTorusIntegralModel.valuation_units_eq_one`, and
`IntegralModel.unramifiedIntegerRange_intersection`. The result is packed into
`IntegralSplitTorusData`. The selected construction and its closedness theorem
use classical choice on this existence result.

## Provenance and limits

This is an internal construction from the named published Library results,
generalizing the unit-fixed-apartment-set input in
`exists_closedSplitIntegralTorus_of_fullRecovery` to arbitrary action subsets.
It does not invoke that theorem. Its algebraic closure step is entirely the
published split-torus closure theorem; this module adds the passage from
pointwise fixation to that theorem's bounded-point hypothesis.

In the intended fixed-pair application, the ambient set can be the two given
building points, or a geodesic once its pointwise fixation is known. The
integral-model hypothesis must still be established independently. This module
proves no apartment-existence or descent statement and does not prove the
fixed-pair special-apartment target.
