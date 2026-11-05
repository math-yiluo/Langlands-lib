# Model homomorphisms over a coefficient square

For commutative domains `R` and `A`, fraction fields `K` and `L`, and specified
algebra structures forming the commuting coefficient square, this module extends
an existing `IntegralModel.Hom` from the `R`/`K` models to their actual `A`/`L`
base changes. The two scalar-tower premises express compatibility of the maps
into `L`. The generic field may change.

`Hom.baseChangeCoefficients` uses the actual pullback of the original model
homomorphism along `Spec A → Spec R`. Its generic homomorphism is exactly the
pullback of the supplied `f` along `Spec L → Spec K`. The new models retain the
specified `baseChangeGenericIso` from `IntegralModel.BaseChange`. The theorem
`baseChangeGenericIso_naturality` transports the original `Hom.generic_comm`
equality through those comparisons, giving the required new compatibility
square. `Hom.baseChangeCoefficients_hom` records the underlying map by reflexivity.

`Hom.isClosedImmersion_baseChangeCoefficients` applies the published
`IsClosedSubgroup.baseChange` to the original closed immersion. Thus the
conclusion concerns the same actual pulled-back homomorphism, without a
flatness requirement on the coefficient map.

This is internal infrastructure derived from actual group-scheme pullbacks and
their natural comparisons. It extends the coefficient-square model constructor;
it complements the fixed-generic-field `BaseChangeHom` interface. It constructs
no model from a generic group, supplies no reductive or parabolic property, and
proves no local covering or maximality statement. Every declaration is uniform
in universe `u`.
