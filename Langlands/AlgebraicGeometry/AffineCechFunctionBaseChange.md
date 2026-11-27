# Scalar extension of the function Čech complex

The affine cover after base change is indexed by the original cover. Its
opens are the inverse images, with charts given by their affine section
rings, and inverse image commutes with tuple intersection.

On each affine intersection the section ring of the inverse image is the
pushout tensor product by `isPushout_fibre`. Taking the finite product of
these algebra equivalences gives `fibreFunctionCochainEquiv`. On a pure
tensor its value is the pullback of the function cochain multiplied by the
new scalar. The pullback commutes with the alternating restriction sums,
so the degreewise equivalences commute with the actual Čech differential.
