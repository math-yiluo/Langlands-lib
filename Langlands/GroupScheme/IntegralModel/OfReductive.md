# The canonical integral model of a reductive group

This is an internal construction from the published `IntegralModel` and
`IsReductive` interfaces. Let \(R\) be a commutative domain, \(K\) its fraction
field, and \(G\) a reductive group scheme over \(\operatorname{Spec}R\).
`IntegralModel.ofReductive` regards \(G\) as an integral model of its actual
base change \(G_K\), with the identity generic-fibre identification. Smoothness
provides the required flatness and finite type; reductivity provides affineness.

`ofReductive_integralPointMap` identifies its integral-point map with
`baseChangeSectionHom`. The comparison theorem says that projection to the
original group through `baseChangeBasePointsEquiv` is restriction of the
section along \(\operatorname{Spec}K\to\operatorname{Spec}R\). The two membership
theorems identify the model's integral-point image with exactly the image of
that restriction map, in either direction of the point equivalence.

The Lean proofs unfold the identity generic-fibre identification and apply
the inverse laws of the existing pullback point equivalence.
`homOfReductive` makes an actual homomorphism of two reductive groups into a
model homomorphism between their canonical models; its generic compatibility
is the identity square. No assertion about integral models other than these
canonical supplied models is made.
