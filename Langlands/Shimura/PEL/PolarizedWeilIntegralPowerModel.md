# Polarization preservation on an exact integral power model

This internal result retains the actual polarized action X, a supplied rational
isomorphism r from an actual abelian scheme B to X, actual dual data W on B,
and a characteristic-zero field structure on the base. It uses the existing
polarized isogeny model on that exact B with that exact comparison. Its actual
polarization is the pullback of the original polarization along the selected
integral multiple of r. Every positive integer is assumed invertible in global
sections, as required for the injectivity of integral Hom into rational Hom.

`multiple_pow` proves that the k-th power of an actual equivariant
self-isogeny with multiplier q has multiplier q^k. It uses the original
multiple equations under composition, with the automorphism multiplication
convention of the categorical endomorphism ring.

`IntegralPolarizedPowerModelStatement` states that, whenever q^k=1 and an
actual integral automorphism g of the specified B rationalizes to the exact
conjugate of that k-th power along r, g preserves the actual polarization of
the specified isogeny model. It also retains the geometric IsPolarization
property of that polarization. No finite-order premise is used.

`integralPolarizedPowerModel` proves the statement. The existing model
comparison has a nonzero square multiplier. Composing its inverse, the k-th
power, and the comparison cancels the comparison multiplier and leaves
multiplier one. Functoriality of automorphism powers identifies the resulting
rational homomorphism with the prescribed rationalization of g. Compatibility
of rational pullback with actual integral dual pullback and injectivity of
integral Hom into rational Hom give the exact integral equality.

The provenance is an internal composition of the imported isogeny-model,
polarization-pullback and integral-Hom results. This result does not assert
finiteness of the polarized automorphism group or finite order of g. Existence
of r, dual data on B and a suitable g remains with the consumer.
