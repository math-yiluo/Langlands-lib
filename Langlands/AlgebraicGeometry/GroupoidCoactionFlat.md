# Flatness over the invariant ring

This internal helper for the Serre criterion uses the unchanged ring étale
equivalence relation and groupoid coactions. Write `A = invariantRing t`.
The conditional assumptions are all-module acyclicity and the assertion that
a coaction with a subsingleton invariant module is itself subsingleton.
The latter assertion is an explicit hypothesis; its Noetherian geometric
proof is not provided here.

For an equivariant map `f`, injectivity of its invariant map forces the
invariants of the kernel coaction to vanish: the invariant kernel inclusion
has image killed by the invariant map of `f`. Zero detection then makes the
whole kernel vanish, proving injectivity of `f`.

For an injective `A`-linear map, the invariant units identify its invariant
scalar extension with the original map. Unit naturality and bijectivity
therefore make that invariant map injective. Applying the kernel argument
proves injectivity after scalar extension to `B`. The definition
`baseChangeEquivRangeOfAcyclic` packages this actual base change as a
`B`-linear equivalence from its domain onto its range. Its application
lemma identifies its value with the original base change.

Mathlib's tensor criterion gives `Module.Flat A B`. If `B ⊗[A] N` is
subsingleton, its invariant submodule is subsingleton, and injectivity of the
unit makes `N` subsingleton. Mathlib's flatness and reflection-of-zero
criterion then gives `Module.FaithfullyFlat A B`. The final theorem expresses
the same property for the ring inclusion `algebraMap A B`.

The injectivity reflection lemma allows the module universe to vary
independently of the ring universe. The scalar-extension and flatness results
use rings and modules in `Type u`, which suffices for Mathlib's flatness and
faithful-flatness criteria when both rings lie in `Type u`.

The provenance is internal algebraic proof infrastructure: kernel coactions,
the arbitrary-module unit, and the pinned Mathlib flatness criteria. This
module proves neither the zero-detection hypothesis nor the full Serre
criterion.
