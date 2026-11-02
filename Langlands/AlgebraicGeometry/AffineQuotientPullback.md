# Pullbacks of affine closed subschemes

This internal helper constructs `affineQuotientPullbackIso φ I`. For a ring
homomorphism `φ : A → B`, it identifies `Spec (B / I B)` with the pullback
of `Spec (A / I) → Spec A` along `Spec B → Spec A`. The two projection
identities record the quotient map on `B` and the induced quotient map from
`A / I`.

The proof first verifies the pushout universal property in commutative rings.
A compatible pair of ring maps kills the extended ideal, so its map from
`B` factors uniquely through `B / I B`. Applying Mathlib's contravariant
`Spec` functor gives a pullback square and the displayed isomorphism.
This derivation uses no finite generation assumption.

`mem_range_SpecMap_quotient_iff` restates Mathlib's range theorem for spectra
of surjective ring maps: a prime is in this closed subscheme exactly when it
contains `I`. This API is intended to identify affine slices cut out by
equations with their scheme pullbacks.
