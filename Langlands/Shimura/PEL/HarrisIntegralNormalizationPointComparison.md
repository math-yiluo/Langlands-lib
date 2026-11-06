# Point independence of integral-normalized Harris levels

This internal supporting construction transports the full integral Tate-image
condition of `HarrisIntegralTateImages` through the original geometric-point
comparisons. It constructs equivalences of the normalized subsets of the
original fixed level sets. All public declarations are in
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`.

Here integral normalization is the additional predicate
`HarrisIntegralFrameCondition` or `HarrisIntegralLevelCondition`. It is distinct
from the normalized signature charts already present in the original CM
presheaf. This module does not identify the two conditions or assert that every
original CM class has an integrally normalized representative.

## Inputs and unchanged objects

The arithmetic types are universe-zero number fields `E` and `F`, with the
stated total reality, total complexity and quadratic extension structures. The
actual algebra `A`, central simple unitary datum `D`, and Harris signature charts
`C` are unchanged. The displayed rational scalar structures and
`Prerequisites` package supply the existing constructions.

The base `S` is a universe-zero quasi-separated scheme. The inputs retain the
relative finite Weil transition statement, rational profinite-integer/adele
comparison `h`, torsion finite-etale statement `htor`, invertibility of every
positive integer on `S`, and finite etale roots of unity at every positive
index. For each of the two field-valued points `s` and `t`, finite fibres of
every finite-etale cover are supplied. The first part assumes an actual
isomorphism `path : fiberFunctor s hs ≅ fiberFunctor t ht`; it does not assume
connectedness, local noetherianity or algebraic closedness of the two fields.

The object `X` is the original `PositivePolarizedAction`, using
`auxiliaryStarRing D C`. Its actual abelian scheme, rational algebra action,
dual geometry, polarization and Weil-compatible frames are retained. The
regular source module is the original finite-adele scalar extension of `A`,
and its integral span is exactly `D.harrisHodgePELIntegralAdeleSpan C`.
The right action and orbit quotient are the original opposite-group action
and `RightOrbit`; no new frame action or orbit equivalence relation is defined.

The finite-adelic compact-open level `K` is an arbitrary original level. No
containment in the integral source stabilizer is required: the level predicate
asks for existence of a normalized representative, and this existence can be
transported directly. Assertions about every representative at stabilizing
levels belong to `HarrisIntegralTateImages`.

## Full Tate-image transport and frame normalization

The private helper `fullImage_transport_iff` proves, for the actual abelian
scheme `B` and every rational Tate element `z`, that `z` is in the image of
`GroupScheme.Tate.toRational` at `s` if and only if its actual
`Tate.rationalTransport` image is in the corresponding image at `t`. The full
integral Tate group and predicate `fun _ => True` are used, so all positive
indices remain present.

In the forward direction, transport an integral preimage by
`Tate.integralTransport` and apply `Tate.toRational_transport`. In the reverse
direction, surjectivity of integral path transport supplies a source integral
element, and injectivity of rational path transport gives its required
rationalization equation. No injectivity of `toRational` is needed.

`harrisIntegralFrameCondition_point` states that the original transported frame
is integrally normalized at `t` if and only if the source frame is integrally
normalized at `s`. Apply the helper to each frame value. The original frame
transport evaluates to rational Tate path transport, while the source vector
and its membership in the fixed Harris integral span remain the same.

## Fixed levels and the restricted equivalence

`harrisIntegralLevelCondition_point` states preservation and reflection of the
existential normalization condition by the original
`Tate.weilAdelicLevelTransport`. A private forward helper transports a normalized
frame witness. The equality of its orbit with the underlying target level
follows by rewriting the witness equality and `RightOrbit.map_mk`. For the
reverse direction, apply that helper to `path.symm` and use the original
`weilAdelicLevelTransport_symm` and equivalence inverse identity.

`harrisIntegralNormalizedLevelPointEquiv` restricts that same original level
equivalence to the subtypes satisfying `HarrisIntegralLevelCondition` at the
two points. Its `_val` theorem is definitional: forgetting the normalization
proof gives the original fixed-level transport on the original level element.

`harrisIntegralNormalizedLevelPointEquiv_path_independent` proves equality of
the restricted equivalences for any two paths with these endpoints. Extensionality
and subtype extensionality reduce this to the published path-independence
result for the original fixed-level transport. Path independence is asserted
for fixed orbit classes, not for individual frames.

## Canonical geometric comparison

The final section additionally assumes `ConnectedSpace S`,
`IsLocallyNoetherian S`, and algebraically closed source and target fields.
`harrisIntegralNormalizedLevelGeometricEquiv` uses the proved
`geometricPathExists` to choose a path and then applies the restricted level
equivalence. Its `_eq_path` theorem proves that every supplied path computes
this same equivalence, using the preceding path-independence result.

`harrisIntegralNormalizedLevelGeometricEquiv_val` identifies its underlying
level map with the component at `K` of the original
`Tate.weilAdelicCompactOpenLevelGeometricTransport`. This equality is
definitional: both constructions choose the path from the same proved
existence statement and use the same original fixed-level transport.

## Provenance and remaining obligations

This unit is an internal consequence of the actual integral/rational Tate
path transports, their rationalization compatibility, the Harris full-image
normalization predicate, and the original Weil frame and fixed-orbit path
comparisons. It translates no additional external theorem. Its generic
full-image observation and one-direction level helper remain private.

It does not prove existence of normalized frames or integral models, removal
of denominators from a rational isomorphism, stability under arbitrary base
change or level transporters, a natural moduli comparison on the full CM test
category, representability, output admissibility, smoothness or projectivity.
The exact `DivisionCMRepresentabilityStatement` of the host task remains open.
