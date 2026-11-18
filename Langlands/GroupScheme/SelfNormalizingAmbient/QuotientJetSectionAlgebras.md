# Actual jet section algebras in supplied and retained ambient coordinates

Let `b : S → Spec R` be a base change and `U` an affine open of `S`.
`IdentityJet.corepresentedBaseChangeJetAlgEquiv` identifies the scalar
extension to `Γ(S,U)` of a supplied corepresenting algebra modulo its
augmentation power with the actual base-changed jet section algebra.
The coordinate map is the pullback projection to the supplied spectrum.

For a closed subgroup with retained quotient-jet data `D`,
`D.originalBaseChangeJetAlgEquiv` uses the retained ambient
quotient and identifies its scalar extension with the actual original
subgroup jet section algebra. The coordinate map is the actual ambient
projection after base change of the original subgroup inclusion.

Both comparisons use the algebra structure from the actual jet
projection. The underlying linear equivalences are the existing jet
section comparisons. On each pure tensor `a ⊗ [c]` their values are `a`
times the restriction of `c` to the actual jet. In particular, the value
at `1 ⊗ [c]` is the actual jet function.

This is an internal application of the tensor-product algebra upgrade.
The existing pure-tensor formulas express the values using the quotient
map of the actual jet module. That map is restriction along the actual
jet inclusion, which is also how `jetCoordinateMap` restricts ambient
coordinates. This identifies the prescribed values in each model and
supplies the algebra equivalences used to evaluate the ambient coordinate
functions on the actual jets.

`IdentityJet.jetSectionScalarTower` applies on every base open. The
`R`-algebra structure on jet functions induced by the composite of
the projection with `b` factors through the `R`-algebra `Γ(S,U)` and
the projection algebra on jet functions. The scalar-tower equality
is the composition rule for the pullback of functions.
