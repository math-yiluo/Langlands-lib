# Actual lifted module charts of the original global face quotients

This internal module for the relative radical filtration proves that each actual
global face quotient is affine and smooth over the original affine base.
It constructs its natural point/section equivalences on every test with a
chosen lift to the original finite affine cover.

Affineness follows from the actual affine quotient construction. Smoothness is
reflected along the actual affine flat surjective cover, through its prescribed
cover isomorphism with the original smooth assembled layer group.

`globalFaceQuotientCharts` uses that same original quotient cover isomorphism
and the constructed natural coordinates of the original assembled layer in
`layerBundle`. Thus the module on the cover and all lifted point charts are
constructed, with varying component ranks and canonical pullback naturality.

This is derived from actual quotient descent, the constructed finite-cover
vector bundle, and multiplicative actual pullback-point transport. It does not
assume or construct the linear overlap cocycle. Proving the global quotient's
vector-bundle predicate requires descending these charts through that cocycle;
this module does not do so.
