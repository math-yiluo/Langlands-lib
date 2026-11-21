# Linearizing a finite-order formal action in character coordinates

For an endomorphism of a finite-coordinate formal module over a field, fix
an eigenbasis of its tangent map and the weight of each basis coordinate.
`ModuleLaw.cyclicProjection` takes the finite weighted average of each
original coordinate series along the iterates of the endomorphism. For an
averaging length invertible in the field and nonzero weights, the derivative
of the average is the original tangent eigenbasis. This follows by taking
linear coefficients in the finite sum.

When the finite power of the endomorphism is the identity and every weight
has the same power equal to one, cyclically shifting the average gives the
exact diagonal formal action. `CoordinateMap.identityCoordinatesOfTangentEquiv`
first removes the linear part by a linear coordinate change, inverts the
resulting identity-linear map, and restores the linear part. It gives both
coordinate maps and both composition equations. `ModuleLaw.cyclicCoordinateIso`
uses the existing identity-idempotent image construction to transport the
actual formal module. Its conjugated endomorphism is the diagonal linear
coordinate map.

This is derived infrastructure for the action of an unramified subfield
unit on a special formal division-order module as in Drinfeld 1976, §2A,
printed p. 109. The tangent-character condition supplies the eigenbasis.
The hypotheses describe the finite-order action that is averaged here.
