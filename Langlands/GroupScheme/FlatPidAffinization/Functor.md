# Canonical affinization and its natural map over an affine base

`affinizationFunctor R` is Mathlib's composite `algΓ R ⋙ algSpec R`.
The displayed structural-map formula identifies its value on `X` definitionally
with the prescribed spectrum of global functions over `Spec R`. Its map on a
morphism is the spectrum map of the morphism on global functions.

`toAffinization R` is the natural morphism from the identity functor to this
functor. Its underlying scheme map at `X` is exactly `X.left.toSpecΓ`.
The over-base compatibility follows from naturality of `toSpecΓ` and the
canonical identification of functions on `Spec R` with `R`; naturality on
morphisms is `Scheme.toSpecΓ_naturality` itself.

This is internal packaging of Mathlib's global-functions adjunction, used in
the canonical-affinization group construction. This file does not assert that
affinization preserves products on arbitrary schemes.
