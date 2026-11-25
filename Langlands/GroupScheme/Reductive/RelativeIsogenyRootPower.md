# Prescribed powers of actual root restrictions over local rings

This internal derived module computes the restriction from
`RelativeIsogenyRootRestriction` using the supplied root-datum factor. The base
is any local commutative ring `R`, including a nonreduced ring. The source and
target group schemes are affine. Their coordinate tori have finite index sets;
`P` and `Q` are supplied reduced fibrewise root data, and
`r : RootDatumIsogeny p Q P` is supplied. The weight map goes from target weights
to source weights. Compatibility on all actual exponent characters and the
ambient torus square are explicit hypotheses. The target is reductive and its
torus is fibrewise maximal. Both actual additive root parametrizations are
supplied. Finiteness of the ambient homomorphism and source reductivity are not
needed here.

`RelativeIsogeny.rootRestrictionCoefficient` is the scalar operation of the
actual root restriction evaluated at `1` in the base ring. The theorem
`rootRestriction_power` computes the operation on every commutative `R`-algebra
`A` as the image of this coefficient times `a ^ r.rootFactor b`.
`rootRestriction_power_rootPoint` computes the ambient composite on every scheme
test as the target root point with coordinate
`baseScalar Z coefficient * a ^ r.rootFactor b`. Tests need not be affine.
The coefficient is not asserted to be a unit in this module.

The generic theorem `IsRootParametrization.restriction_powerWeight` cancels the
monic target parametrization and uses the two all-test conjugation laws and the
ambient torus square. The target character pulls back to the prescribed natural
multiple of the source character. Evaluation converts this character multiple
to a power. Laurent substitution along the source coroot has degree two,
by the supplied fibrewise pairing and the root-coroot identity. Thus
`rootRestriction_hasLaurentPower` invokes `NaturalPowerRigidity` to determine the
coefficient operation on every algebra over the whole base ring.

The generic `rootPoint_eq_of_scalarOperation` evaluates a proposed coefficient
formula at the identity point of the additive group over its own coordinate
algebra. Pullback along any scalar point gives the formula on every scheme test,
including nonaffine tests. `rootRestriction_power_rootPoint` then composes with
the actual ambient restriction square. No equality over the base is inferred
from field fibres. All results are derived from the imported actual root
restriction, root equivariance and natural Laurent-polynomial rigidity APIs;
this module does not assert the full isogeny rigidity theorem.
