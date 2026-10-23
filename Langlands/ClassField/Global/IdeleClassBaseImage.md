# Idele-class cohomology after replacing the base field by its image

Let `F : Type u` and `E : Type v` be fields, with `Algebra F E`. The
bottom intermediate field `F₀ = (⊥ : IntermediateField F E)` is the image
of the algebra map inside `E`, so its carrier belongs to `Type v`.
Mathlib's `IntermediateField.botEquiv F E` identifies it with `F`.
The universes `u` and `v` are independent.

`baseImageAutEquiv F E` identifies the groups of automorphisms of `E`
over `F` and over `F₀`. Both maps use `AlgEquiv.restrictScalars`, using
the two scalar towers provided by Mathlib. The underlying field map is
unchanged in both directions; the evaluation lemmas state this explicitly.
The inverse and multiplicativity identities follow by extensionality on `E`.
No Galois or finite-dimensional hypothesis is required for this construction.

When `E` is a number field, `relativeIdeleClassAut_baseImage` states that
the two arithmetic actions are the same under this automorphism-group
equivalence. This is a definitional identity: the published action uses
the underlying ring automorphism of `E`. In particular, the carrier of
the idele-class group remains the actual `IdeleClassGroup (𝓞 E) E`.

`relativeIdeleClassCohomologyBaseImageIso F E n` is an isomorphism
between the published ordinary cohomology modules in every degree `n`.
It applies Mathlib's `groupCohomology.mapIso` to the automorphism-group
equivalence and the identity linear equivalence on the unchanged
additive idele-class coefficient module. The equivariance condition is
definitional. Both sides use the original scalar ring
`NormalizedTwoCocycle.CoefficientScalars.{v}`; no coefficient lift or
alternative cohomology model is introduced.

This is internal derived content, obtained from Mathlib's bottom
intermediate-field scalar towers and group-cohomology functoriality,
and the Library's actual arithmetic idele-class action. It invokes no
external arithmetic theorem. It is intended to support reducing the
independent-universe global Herbrand problem to two number fields in
the same universe. This module constructs only the transport: it does
not assert the Herbrand quotient, cohomology finiteness, or a local
unit computation.
