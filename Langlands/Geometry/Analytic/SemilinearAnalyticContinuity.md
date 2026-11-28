# Continuity tests for actions on analytic spaces with varying fields

Berkovich's *Étale equivariant sheaves on p-adic analytic spaces*, retained
`Equish_1996` manuscript, §1.1, printed and PDF pp. 1–2, uses compact analytic
domains and functions to test continuity of an action. An automorphism close
to the identity preserves the test domain, and on the domain the spectral
seminorm of the difference between the pullback of the test function and the
function itself is at most the specified positive real bound.

`SemilinearAffinoidProbe` represents an affinoid domain by a compatible
presentation with a greatest chart and an actual inclusion. The bounded
algebra of this chart is the full section algebra of the probe.
`SemilinearAffinoidProbe.IsNearIdentity` requires the automorphism to restrict
to an automorphism of this domain in the varying-field analytic category. Its
analytic component has target the scalar extension of the probe along its
field map. A common strong representative gives the bounded restriction of the
original function and the pullback of its scalar extension. The difference is
tested at each spectrum point of this representative. The denominator of the
representative is a quasi-isomorphism.

For the identity, the denominator is the unit projection from the
identity scalar extension. On each chart the pullback of the scalar-extended
function agrees with the original restriction followed by the coefficient
unit map, so the difference vanishes. For any passing test, applying the
underlying-space functor to the analytic square and using surjectivity of the
probe automorphism shows that the action preserves the probe's point locus.

`IsContinuousSemilinearAction` requires the tests to hold on a neighbourhood
of the identity for every probe, function and positive bound. Intersecting
the resulting neighbourhoods gives simultaneous control of finitely many
tests. The passage to the compact-domain criterion in §1.1 uses a finite
affinoid covering of the compact domain and the restrictions of its
functions. This passage and continuity of completed scalar extension for
these tests are separate assertions.
