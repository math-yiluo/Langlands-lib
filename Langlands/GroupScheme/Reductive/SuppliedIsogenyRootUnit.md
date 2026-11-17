# Unit coefficients of supplied root restrictions over arbitrary rings

This internal derived module extends the finite-root unit formula to every
commutative ring `R`, including nonreduced and zero rings. The source and target
group schemes are affine, with supplied finite coordinate tori, full reduced
fibrewise root data `P` and `Q`, a root-datum isogeny
`r : RootDatumIsogeny p Q P`, and actual compatibility on every fixed-exponent
character. The ambient homomorphism has the supplied torus square, the target
is reductive with a fibrewise maximal torus, and actual additive source and
target root parametrizations are supplied. The ambient homomorphism is finite.
No local-ring or nontriviality assumption, source reductivity, or flatness or
surjectivity of that homomorphism is needed.

In the namespace `SuppliedRootIsogeny`, `rootRestriction_isFinite` proves that
the actual additive root restriction is finite. The source parametrization is
a closed immersion, so its composite with the finite ambient homomorphism is
finite. The exact restriction square identifies this composite with the
restriction followed by the target parametrization. That parametrization is
a closed immersion and hence separated, so finiteness cancels through it.

`isUnit_rootRestrictionCoefficient` applies the imported arbitrary-ring theorem
`LocalSplitCell.isUnit_coefficient_of_power_of_isFinite` to this finite
restriction and the power formula from `SuppliedIsogenyRootPower`. The generic
theorem uses coefficient base change, epimorphic finite additive-line maps
over fields, and nonvanishing in all field algebras to detect a unit. Its proof
already treats arbitrary rings; no new field-fibre argument or local-ring
choice is introduced here. The arbitrary-ring power formula also includes
the zero ring.

`rootRestrictionUnit : Rˣ` chooses the unit represented by this coefficient;
`coe_rootRestrictionUnit` states the equality of its underlying scalar with
`rootRestrictionCoefficient`. `rootRestriction_unit_power` gives the
unit-coefficient power formula on every commutative coefficient algebra.
`rootRestriction_unit_power_rootPoint` states the ambient formula on every
scheme test: the source root point of coordinate `a` followed by the ambient
homomorphism is the target root point of coordinate
`baseScalar Z (rootRestrictionUnit : R) * a ^ r.rootFactor b`.
Tests need not be affine or reduced.

The derivation reuses the published finite-morphism cancellation and generic
unit-coefficient theorem and the new arbitrary-ring supplied-root power
formula. It preserves the existing local-ring `RelativeIsogeny` declarations.
Existence of the supplied root-datum isogeny and coordinates, comparison on
opposite roots, and the full torus-conjugacy rigidity theorem remain separate
obligations.
