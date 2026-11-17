# Generic pullbacks of connected étale schemes over a DVR

Worker 607. This internal helper unit derives its conclusions from the published
fraction-field/generic-point comparison, the published flat DVR connectedness
theorem with reduced special fibre, and reducedness for smooth schemes over a
reduced base. It introduces no external-source theorem or new hypothesis on the
residue field.

For any commutative domain R and specified fraction field K, the theorem
`isDominant_fractionFieldMap` proves that the original morphism
`Spec.algebraMap R K` is dominant. The generic point is dense, its residue-field
spectrum has precisely that point as its image, and the published comparison
identifies the chosen fraction-field morphism with that map composed with an
isomorphism.

`genericPullbackIsoFiber` defines the actual isomorphism between the chosen
fraction-field pullback of any scheme over Spec R and its residue-field fibre
at the generic point. It is the base-change map induced by the published
fraction-field/generic-point comparison, with identity on the original scheme
and base. All three comparison maps are isomorphisms, so the pullback map is
an isomorphism. This construction only needs the domain hypothesis.

For a discrete valuation ring R and a connected scheme U étale over Spec R,
`connectedSpace_etale_genericPullback` proves that its actual pullback along
`Spec.algebraMap R K` is connected. Its special fibre is smooth over a field and
therefore reduced. The published
`FlatReducedDvrConnectedness.connectedSpace_genericFiber_of_reduced_specialFiber`
then gives connectedness of the residue-field generic fibre. Base change of the
fraction-field comparison is an isomorphism and transports that connectedness to
the specified pullback. No surjectivity or quasi-compactness of U over Spec R is
assumed.

These lemmas do not assert extension of generic sections or existence of finite
outer-class carriers. They are geometric inputs to the remaining section
extension argument.
