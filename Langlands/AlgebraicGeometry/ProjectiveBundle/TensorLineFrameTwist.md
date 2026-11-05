# Tensor-line degree one on the fixed projective frame bundles

Let `S : Scheme.{u}`, let `M` be an actual module sheaf locally free of
fixed rank `n + 1`, and let `N` be an actual locally free rank-one module
sheaf on `S`. The existing `frameBundleIso` is the scheme isomorphism
from the fixed tensor frame bundle to the fixed source frame bundle.
Write `F` for its forward map and `p` for the tensor bundle's structure
map to `S`.

`frameSourceTensorTwistModule` is the actual module
`F* O_source(1) ⊗ p* N` on the fixed tensor frame bundle.
`frameBundleTwistIso` constructs the global isomorphism

`O_tensor(1) ≅ F* O_source(1) ⊗ p* N`.

The two local-freeness hypotheses are its only geometric assumptions.
The fixed frame bundles, their scheme isomorphism, and the degree-one
isomorphism are all constructed from them. In particular, there is no
chosen global trivialization of `N` or extra gluing-compatibility premise.
`frameBundleTwistLineIso` lifts the same module isomorphism to the full
subcategory of actual line bundles. Its tensor uses the proved
unconditional invertibility of the canonical pullback tensor comparison.

The proof transports the established joint-atlas comparison
`tensorLineTwistIso` along the inverse of the tensor atlas's isomorphism
with its fixed frame bundle. For the source degree-one factor,
`sourceTwistToFrameIso` applies the canonical composition comparison twice:
the composite of the inverse tensor-atlas comparison, the joint-atlas
isomorphism, and the source-atlas comparison is exactly `F`.
For the base-line factor, the inverse atlas comparison commutes with the
structure maps to `S`. The actual invertible pullback tensor comparison
and the tensor of these two factor isomorphisms give
`sourceTensorTwistToFrameIso`.

Finally, the degree-one module on the tensor atlas is by definition the
pullback of fixed degree one. The canonical composition comparison for
the inverse and forward atlas maps, followed by identity pullback, cancels
these two pullbacks. Composing its inverse, the inverse-atlas pullback of
`tensorLineTwistIso`, and `sourceTensorTwistToFrameIso` gives the displayed
fixed-bundle formula.

This is an internal derived consequence of the genuine frame-atlas
constructions, their already proved global tensor-line comparison, and
canonical pullback composition and tensor comparisons. It introduces no
new literature assertion. A relative cubic embedding and ordinary
polarized full-level moduli representability remain further work.
