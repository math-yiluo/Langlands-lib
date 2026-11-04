# Integral preimages under actual proper model morphisms

This is a derived statement ingredient of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed p.11, Proposition 4.4,
second paragraph of the proof. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`ValuationRingPointPreimageStatement` says the following. Let `C → R → L` be a
compatible scalar tower of commutative rings, where `R` is a valuation domain
and `L` is its fraction field. For any universally closed morphism `f : X → Y`
of schemes over `Spec C`, the inverse image in `X(L)` of the image of `Y(R)`
is the image of `X(R)`. All these are actual relative scheme points
`RingPoint C X A`, namely morphisms `Spec A → X` over `Spec C`. Extension of
coefficients is the existing `RingPoint.changeRing`, induced by the actual
spectrum map of the inclusion `R → L`. The map on points is postcomposition
with `f`. Images are set-theoretic ranges: neither integral-point injectivity
nor a topology is assumed.

The generic assertion uses the existence part of Mathlib's valuative criterion
for universally closed morphisms. Properness suffices, but finite type and
separatedness of the model or its target are unnecessary for this particular
equality. This generality is derived from that criterion, rather than asserted
as the literal scope of Conrad's global-field proposition.

`CurvePlaceLocalIntegralPreimageStatement` specializes the equality to the
actual curve-place completions and their completed valuation rings at every
place outside a finite `S`. The base is the original `curvePlaceSIntegers`.
`NumberFieldLocalIntegralPreimageStatement` gives the same assertion for every
finite place outside `S` of any number field, with base the original
outside-`S` integer ring. Both quantify over arbitrary models and proper
morphisms over that base. They impose no affineness condition.

In each arithmetic clause `R` is the integral factor of the existing
`CurvePlaceLevelFactor` or `NumberFieldLevelFactor`. Its scalar action is the
published one, induced by the original level-ring diagonal. The action on `L`
is the original integer-subring inclusion into the global field followed by
completion. The `commutes'` equation in the displayed algebra homomorphism
`ι` is proved by reflexivity: inclusion of the integral factor into its fraction
field agrees definitionally with this original scalar action. Thus the statement
uses the original arithmetic maps, not an independently chosen action.

The combined `AdelicLocalIntegralPreimageStatement` is exactly the conjunction
of these three proposition definitions in arbitrary common universe `u`.
The curve clause applies even to arbitrary constant fields and arbitrary
extensions with the specified actual discrete curve places; finite constants
and the global-function-field condition are not needed for this algebraic
ingredient. Both arithmetic clauses allow empty `S`. Infinite number-field
places have no outside-`S` integral factor, so this local assertion concerns
finite places only.

This pair states the local valuative equality; it does not prove it or assert
existence of proper spread models, a full-level preimage equality, properness on
full adelic points, or eventual stabilization. Those are separate obligations
of the whole-paper development.
