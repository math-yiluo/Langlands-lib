module

public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.ShortExact
import StacksFrontier.RingTheory.Depth.RingEquiv

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Transport of Cohen–Macaulayness between local rings

A Noetherian local ring is Cohen–Macaulay exactly when it is a maximal Cohen–Macaulay module
over itself, and Cohen–Macaulayness only depends on the isomorphism class of the ring.

## Main results

* `isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay` identifies
  `IsCohenMacaulayLocalRing R` with `Module.IsMaximalCohenMacaulay R R`.
* `isCohenMacaulayLocalRing_iff_of_ringEquiv` transports Cohen–Macaulayness along a ring
  isomorphism of Noetherian local rings.
* `Module.depth_eq_depth_self_of_surjective_algebraMap`: for a surjective algebra map `A → B` of
  local rings, the depth of `B` along the maximal ideal of `A` is the self-depth of `B`.

## Implementation notes

`IsCohenMacaulayLocalRing` is defined as equality of the depth *supremum* with the support
dimension, whereas `Module.IsMaximalCohenMacaulay` uses `Module.depth`. The two agree because
the maximal ideal of a local ring does not annihilate the ring.

## References

* [Stacks Project, Tag 00N8](https://stacks.math.columbia.edu/tag/00N8)
-/

@[expose] public section

open RingTheory.Sequence

/-- A Noetherian local ring is Cohen–Macaulay exactly when it is a maximal Cohen–Macaulay
module over itself. -/
public theorem isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay (R : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ Module.IsMaximalCohenMacaulay R R := by
  rw [isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self,
    IsCohenMacaulayModule, Module.IsMaximalCohenMacaulay]
  change Module.depthSup R (IsLocalRing.maximalIdeal R) R = Module.supportDim R R ↔ _
  rw [Module.supportDim_self_eq_ringKrullDim, Module.depthSup_eq_iSup,
    Module.stacksDepth, ite_eq_right (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)]

/-- Cohen–Macaulayness of a Noetherian local ring depends only on its isomorphism class. -/
public theorem isCohenMacaulayLocalRing_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsCohenMacaulayLocalRing A ↔ IsCohenMacaulayLocalRing B := by
  rw [isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A,
    isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B]
  exact Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e
