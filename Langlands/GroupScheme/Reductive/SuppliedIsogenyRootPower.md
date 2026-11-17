# Prescribed powers of supplied root restrictions over arbitrary rings

This internal derived module computes the supplied-root restriction from
`SuppliedIsogenyRootRestriction` over any commutative ring `R`. The source and
target group schemes are affine, with supplied finite coordinate tori and full
reduced fibrewise coordinate root data `P` and `Q`. A root-datum isogeny
`r : RootDatumIsogeny p Q P`, an actual compatible torus homomorphism on all
fixed-exponent characters, and its ambient torus square are supplied. The
target is reductive and its torus is fibrewise maximal. Actual additive
parametrizations of the corresponding source and target roots are explicit
inputs. Neither locality nor nontriviality of the ring, source reductivity,
or finiteness, flatness or surjectivity of the ambient homomorphism is needed.

In the namespace `SuppliedRootIsogeny`, `rootRestrictionCoefficient` evaluates
the scalar operation of the actual additive restriction at `1` in the base
ring. `rootRestriction_hasLaurentPower` proves that this operation has Laurent
degree `2 * r.rootFactor b` on the degree-two Laurent monomial.
`rootRestriction_power` then computes it on every commutative `R`-algebra `A`
as the image of this one coefficient times `a ^ r.rootFactor b`.
`rootRestriction_power_rootPoint` gives the ambient formula on every scheme
test, without an affineness or reducedness restriction on that test:

`rootPoint u Z a` followed by the ambient homomorphism equals the target root
point with coordinate `baseScalar Z coefficient * a ^ r.rootFactor b`.

The proof of Laurent degree splits according to whether the base ring is
trivial. Over the zero ring, its Laurent polynomial ring is subsingleton, so
the Laurent identity holds. In the nontrivial branch,
`IsFibrewiseRootDatumOf.pairing_of_nontrivial` and the root-coroot identity give
the coordinate pairing two. The generic all-test theorem
`IsRootParametrization.restriction_powerWeight` from
`RelativeIsogenyRootPower` cancels the monic target root parametrization and
uses actual torus equivariance and the restriction square. The supplied
weight-map equation identifies the ratio of characters with the positive
root-datum factor. `hasLaurentPower_of_weight` applies this identity along
the source coroot. The generic Laurent-polynomial rigidity theorem then
determines the scalar operation on every algebra.

Finally, the imported `rootPoint_eq_of_scalarOperation` transports the
coefficient formula from the universal additive coordinate to every scheme
test, and the actual restriction square identifies its ambient composite.
No equality of morphisms over the base is inferred from equality on field
fibres. This derivation reuses the generic Laurent and root-point helpers,
leaving the published local-ring API unchanged. The coefficient's unit
property, torus alignment and full isogeny rigidity theorem are subsequent
obligations.
