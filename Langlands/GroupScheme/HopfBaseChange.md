# Hopf spectra and scalar extension

This internal construction packages the existing Mathlib Hopf-algebra and
scheme-pullback comparison as an isomorphism of actual group schemes. It uses
`AlgebraicGeometry.hopfSpec`, `AlgebraicGeometry.pullbackSpecIso'`, the
multiplication-preserving comparison at the end of
`Mathlib.AlgebraicGeometry.Group.Affine`, and the tensor-product Hopf instance
from `Mathlib.RingTheory.HopfAlgebra.TensorProduct`. No additional result from
external literature is asserted.

For commutative rings `R`, `S`, and `A` in an arbitrary universe `u`, an
`R`-algebra structure on `S`, and a Hopf `R`-algebra structure on `A`,
`HopfCoordinates.scalarExtension R S A` is the commutative Hopf `S`-algebra
`S ⊗[R] A` with Mathlib's standard tensor-product structure. Neither flatness
nor a field hypothesis is required.

`HopfCoordinates.baseChangeSpecIso R S A` identifies the pullback of the
relative Hopf spectrum of `A` along `Spec S → Spec R` with the relative Hopf
spectrum of `S ⊗[R] A`. Its underlying scheme map first exchanges the two
factors of the pullback and then uses `pullbackSpecIso'`. Mathlib proves this
map preserves identity and multiplication. The construction makes that
instance explicit after viewing the comparison as an isomorphism in
`Over (Spec S)`, then applies `Grp.mkIso'`. Thus the result respects the actual
group-scheme structure, including inversion.

This comparison supplies no descent of group-like elements, character-lattice
identification, torus-splitting theorem, or dynamic-centralizer reductivity
proof. Those remain separate obligations in the parent task.
