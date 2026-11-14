# Hopf-coordinate bridge for finite-index enlargement

This internal module derives the coordinate and scheme comparisons required by
the finite-index enlargement proof from the published affine Hopf-spectrum
isomorphism, Mathlib's convolution-point equivalence, and the actual pullback
point comparison of `IntegralModel`.

The coordinate equivalence sends an algebra homomorphism to its spectrum followed
by the coordinate isomorphism. Applying the inverse generic-fibre isomorphism and
the pullback-point comparison therefore identifies generic rational points with
fraction-field-valued coordinate maps, as a multiplicative equivalence. Integral
sections have the analogous base-ring coordinate description. Smoothness and
flatness of the coordinate algebra follow by transporting the structural
morphism across the coordinate isomorphism and applying the affine ring-map
criteria.

The comparisons allow any supplied Hopf-spectrum isomorphism, so the same
integral-point criterion applies to the canonical coordinates and to a supplied
Hopf spectrum. Scalar extension of the coordinate map of an integral section is
its generic evaluation. Conversely, an algebra map whose values all lie in the
image of the base ring lifts through that image using the injectivity of the
fraction-field inclusion. This proves the integral-point criterion.

A smooth Hopf algebra and a Hopf map with bijective generic tensor map yield
an actual reconstructed integral model. Tensor-spectrum naturality makes the
base-changed map an isomorphism of schemes. Reflection through the over category
and lifting to group objects give the required generic group isomorphism.
Smoothness supplies flatness and finite type; the affine spectrum supplies
affineness. Composing the Hopf-spectrum map with the coordinate isomorphism
preserves the supplied open-immersion property. The generic isomorphism was
chosen so that the model morphism extends the generic identity.

Finally, `reconstructedModel_evaluationEquiv` computes evaluation in the
reconstructed model, taken with the identity coordinate isomorphism of its own
Hopf spectrum. It equals evaluation in the original model followed by
restriction along the Hopf map. The proof compares spectra. It applies
`evaluationEquiv_spec` to both models, unfolds the generic isomorphism of the
reconstructed model through the pullback of the enlargement map, and cancels the
coordinate isomorphism of the original model against its inverse. Combined with
the integral-point criterion,
`reconstructedModel_mem_integralPoints_iff` states the following: a generic
point is integral for the reconstructed model exactly when every element of the
Hopf algebra, mapped into the original coordinates, has an integral value.

No external statement or additional mathematical premise is introduced.
