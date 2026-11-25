# Unit coefficients of finite actual root restrictions

This internal derived module proves that finiteness makes the coefficient in
`RelativeIsogenyRootPower` a unit. The base is an arbitrary local commutative
ring `R`, including nonreduced rings. The source and target group schemes are
affine, with supplied finite coordinate tori and reduced full fibrewise root
data `P` and `Q`. A root-datum isogeny `r : RootDatumIsogeny p Q P`, compatibility
of its weight map with the actual torus homomorphism on every exponent
character, and the ambient torus square are supplied. The target is reductive
with a fibrewise maximal torus. Actual additive parametrizations of the
corresponding source and target root functors are also supplied. The new
hypothesis is finiteness of the ambient homomorphism `phi`; source reductivity
and flatness or surjectivity of `phi` are not required.

`RelativeIsogeny.rootRestriction_isFinite` first proves that the actual additive
restriction is finite. The source parametrization is a closed immersion, so
its composite with `phi` is finite. The restriction square expresses this
composite as the restriction followed by the target parametrization. That
parametrization is a closed immersion, hence separated; finiteness cancels
through this postcomposition.

The generic theorem
`LocalSplitCell.isUnit_coefficient_of_power_of_isFinite` applies over any
commutative ring. It takes a finite additive-line endomorphism and a supplied
power formula `c * a ^ q` on every coefficient algebra and proves `IsUnit c`.
There is no separability hypothesis or condition on the exponent. Its proof
uses the following actual morphism comparisons:

- `baseChangeEndomorphism A f` is the coefficient base change of `f`,
  transported to the standard additive group over `A` on both sides.
  `gaCoord_baseChangeEndomorphism` identifies its coordinate with the original
  coordinate on the same test scheme over `R`.
- `isFinite_baseChangeEndomorphism` uses the underlying Cartesian square and
  the coordinate isomorphisms to preserve finiteness.
- Over a field, `epi_of_isFinite` uses the standard one-dimensional vector
  coordinates to give smoothness, connectedness and affineness. The imported
  finite-homomorphism theorem for equal Lie dimensions gives flatness and
  surjectivity, hence an epimorphism.
- `coefficient_ne_zero_of_epi` shows that a zero coefficient in an all-test
  power formula makes the map the identity-valued constant morphism. Cancelling
  this epimorphism would make the identity morphism of the additive line
  constant. The coordinate of the scalar point `1` contradicts this over a
  field.

The supplied formula is transported to each field algebra using the universal
coordinate comparison from `rootPoint_eq_of_scalarOperation` and the explicit
base-scalar comparison. Thus the coefficient is nonzero in every field algebra.
`NaturalLine.Operation.isUnit_value_one_of_fields` detects units by reduction
modulo maximal ideals; the given power formula identifies the base value at
one with `c`. Field fibres are used only to detect the unit property. They do
not detect equality of morphisms over the base.

`RelativeIsogeny.isUnit_rootRestrictionCoefficient` applies this generic result
to the finite actual restriction and its previously proved power formula.
`rootRestrictionUnit : Rˣ` chooses its unit, and `coe_rootRestrictionUnit`
identifies its underlying scalar with `rootRestrictionCoefficient`.
`rootRestriction_unit_power` states the resulting formula on every coefficient
algebra. `rootRestriction_unit_power_rootPoint` states the ambient formula
on every scheme test:
the image of the source root point of coordinate `a` is the target root
point of coordinate
`baseScalar Z (rootRestrictionUnit : R) * a ^ r.rootFactor b`.
Tests need not be affine or reduced.

All constructions are derived from the imported root-restriction, natural
power, additive base-change and finite-homomorphism APIs. Existence of the
supplied root-datum isogeny, opposite-root comparison and assembly of the full
torus-conjugacy rigidity theorem are not part of this module.
