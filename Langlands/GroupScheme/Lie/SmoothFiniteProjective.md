# Finite projectivity of the actual smooth affine Lie module

For a smooth affine group scheme `G` over the spectrum of any commutative
ring `R`, this file proves that the actual dual-number Lie module
`Additive (lieKernel G R)` is finite and projective over `R`. There is
no field, reducedness, noetherian, connectedness or supplied-coordinate
basis assumption.

The construction uses the existing actual affine coordinate presentation
`Lie.coordinateAlgebra G` and its actual identity augmentation
`Lie.coordinateOrigin G`. `identityCotangent` is
`R ⊗[coordinateAlgebra G] KaehlerDifferential R (coordinateAlgebra G)`,
where the coordinate algebra acts on `R` through that augmentation.
It is the pullback of the coordinate differential module to the actual
identity section.

`identityCotangentDualEquiv` combines the tensor extension/restriction
adjunction `LinearMap.liftBaseChangeEquiv` with the universal property
`KaehlerDifferential.linearMapEquivDerivation`. Composing its inverse
with the existing actual-kernel derivation equivalence constructs
`kernelIdentityCotangentDualEquiv`. Thus the claimed Lie module is
identified with the actual dual of this cotangent module.

The published coordinate smoothness bridge proves that the chosen
coordinate algebra is smooth over `R`. Mathlib then supplies finiteness
and projectivity of its Kähler differentials. Scalar extension to the
identity augmentation preserves those properties. The dual of a finite
projective module is finite projective, and transport across the
constructed Lie-kernel equivalence proves the two instances.

The provenance is internal: the construction and proof combine the
published actual affine-kernel derivation model and coordinate smoothness
bridge with Mathlib's tensor, differential and projective-module results.
This supplies actual finite projectivity for the relative adjoint-weight
argument; local weight-rank constancy and reductive-locus openness are
separate obligations.
