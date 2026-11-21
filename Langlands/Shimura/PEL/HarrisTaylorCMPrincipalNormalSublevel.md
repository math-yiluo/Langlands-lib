# Reduction of ordinary Harris representability to principal levels

This internal reduction combines the published normal-sublevel decomposition
of the division-case target with the actual Harris principal congruence
subgroups. It does not construct a moduli scheme. Its only new proposition,
`DivisionCMPrincipalOrdinaryRepresentabilityStatement`, is a smaller target
for the ordinary-moduli route.

## Principal normal refinements

`exists_smallCMPrincipalNormalSublevel` starts with an original small Harris
level `U` whose Hodge transport stabilizes the actual integral source span,
and a positive integer `M`. By the cofinality theorem
`exists_harrisIntegralAdeleCongruence_le`, the transported open subgroup of
`U` contains `K(k)` for some positive `k`. Put `m = k M`; divisibility gives
`K(m) ≤ K(k)`. The level `V` is the preimage of the open subgroup `K(m)`
under the same continuous Hodge-coordinate isomorphism used by
`hodgeLevelFunctor`. It is open; it is contained in `U`, hence compact as a
closed subset of a compact set; and it is small because smallness passes to
subgroups. Its transport is exactly `K(m)`, and `M` divides `m`.

`V` is normal in `U` relative to `U`. Conjugating an element of `V` by an
element of `U` is computed after the multiplicative Hodge transport. The
transported element of `U` lies in the integral stabilizer by hypothesis.
`harrisIntegralAdeleCongruence_normal` proves `K(m)` normal in that
stabilizer, so the conjugate lies in `K(m)` again.

## The reduction

`DivisionCMPrincipalOrdinaryRepresentabilityStatement D C h P
dualityNaturality compatibility htor M` says: if `D` is a division algebra,
then every original small level whose Hodge transport is equal to `K(m)` for
a positive multiple `m` of `M` carries the existing ordinary quasi-projective
representation data, `CMOrdinaryQuasiProjectiveRepresentation`. Such a level
automatically lies in the integral stabilizer, and the statement quantifies
over that proof of containment.

`divisionCMNormalSublevelRepresentabilityStatement_of_principalOrdinary`
proves the published `DivisionCMNormalSublevelRepresentabilityStatement` from
this principal statement and the published
`CMQuasiProjectiveNormalQuotientStatement`. Given a small level `U`, the
published refinement `exists_smallCMNormalSublevel_le_hodgeOpenSubgroup`
first gives a small level `W ≤ U`, normal in `U`, whose transport lies in the
stabilizer. The previous construction gives a principal `V ≤ W`, normal in
`W`. The principal statement represents the ordinary problem at `V`, and
`CMOrdinaryQuasiProjectiveRepresentation.toQuasiProjective` gives the
original quasi-projective data there. The normal-quotient premise, applied
to `V` normal in `W`, gives quasi-projective data at `W`. Thus `W` is the
required normal sublevel of `U`. Only one application of the normal-quotient
premise is used; `V` need not be normal in `U`.

The divisibility condition on `m` lets the ordinary construction impose a
lower bound on the principal modulus, such as a multiple of a fixed
integer at least three, as is customary for rigidity of full level
structures. The module makes no claim about which moduli are sufficient.
