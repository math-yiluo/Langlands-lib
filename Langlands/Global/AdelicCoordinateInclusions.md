# Shared additive coordinate inclusions into the actual adeles

Author: Worker 1692. These existing constructions are moved unchanged from
`Factors/HeckeAdditiveComponents` to a shared module importing only `Adelic`.
Their full names remain in `Langlands.Global.HeckeFunctionalEquation`.

For a number field `K : Type u`, `finiteAdditiveInclusion K v` inserts an
additive element of the actual finite completion into the full adele ring,
with zero at every other coordinate. `infiniteAdditiveInclusion K v` does the
same for an archimedean completion. Both are additive group homomorphisms,
with exactly their original definitions and independent choice of the place.

`continuous_finiteAdditiveInclusion` factors the single-coordinate map through
the restricted-product stage allowing an exception at the selected place.
That stage has the ordinary product/subspace topology, and its inclusion
into the cofinite restricted product is continuous.
`continuous_infiniteAdditiveInclusion` uses continuity of the ordinary
single-coordinate product map.

The arithmetic objects and topology conventions are those of [Adelic](Adelic.md).
These internal derived maps are shared by
[additive-character restrictions](Factors/HeckeAdditiveComponents.md) and
[adelic local approximation](AdelicLocalApproximation.md).
No global duality or character nontriviality result is asserted here.
