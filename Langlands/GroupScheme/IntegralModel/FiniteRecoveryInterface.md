# Existential finite recovery and the final descent assembly

This internal interface packages the remaining finite-coefficient existence
input separately from the completed descent construction. It uses arbitrary
common universe `u` and the actual nonarchimedean local field, inertia fixed
field, spectral integer rings and canonical coefficient inclusions.

For a finite-stage field `E` contained in the inertia fixed field,
`HasFiniteRecoveryAt F E G P` means that there is an actual integral model
`N` of `baseChanged F E G` whose coefficient extension is isomorphic to the
original model `P`. The generic map is exactly `finiteInertiaGenericIso`,
the canonical direct-versus-iterated field pullback comparison. The
coefficient algebras come from `IntermediateField.inclusion` and
`spectralIntegerInclusion`; the mixed algebra is their field composite.
Smoothness of `N` is not an input.

`HasFiniteUnramifiedRecovery F G P` additionally quantifies over `E` and
records its containment, finite dimension, Galois property and arithmetic
unramifiedness. `FiniteUnramifiedRecoveryStatement` asks for such a recovery
for every smooth original model `P`. These are proposition definitions,
not existence theorems.

`descent_of_finiteRecoveryAt` opens an existential recovery at an abstract
field and applies `modelOfFiniteRecovery`, which reflects smoothness from
`P`, constructs the descent datum using stable integral points and the
supplied extension statement, and makes that datum effective.
`descent_of_finiteUnramifiedRecovery` first opens the field existential and
installs its arithmetic witnesses before applying that construction.
Both yield a smooth model over the **given** valuation integers, with an
actual `baseChangeUnramified.Iso P (Iso.refl _)`.

Finally, `unramifiedSmoothModelDescent_of_extension_of_finiteRecovery`
assembles the precise published descent statement from two explicit
premises: `SmoothHomExtensionStatement` and
`FiniteUnramifiedRecoveryStatement`. This is an internal composition of
the existing finite-recovery and arithmetic adapters. It proves neither
premise and is not an unconditional proof of KP Fact 2.10.16 or completion
of the host task. The original target pair and its imports are unchanged.
