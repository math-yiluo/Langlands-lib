# Archimedean polynomial bounds for adelic rectangles

This internal module defines `rectangleArchimedeanCoordinates` by
applying the published infinite-adele mixed-space equivalence to every
rectangular entry. Matrix norms in this module are the elementwise
supremum norms (`Matrix.Norms.Elementwise`).

For a standard-compact Iwasawa factorization of the actual rectangular
chart, let `Y` be the mixed coordinates of its idelic simple-root row.
The theorem bounds the norm of the whole archimedean rectangle by
`(1+‖Y‖)^(d*(d+1)) * (d+1)!`. The exponent and constant depend only
on the number of rectangular rows, and the bound is independent of
the leading block.

The implemented proof first transports the local norm estimate through
an arbitrary ring homomorphism to a normed field. The diagonal of the
projected upper triangular factor is the projection of the given
idelic diagonal, so its trailing ratios satisfy the same common
bound. At each real or complex place, the published standard compact
membership gives an orthogonal or unitary matrix; its entries, and
those of its inverse, have norm at most one. Every individual root
coordinate is bounded by the mixed-space norm of `Y`. Applying the
local estimate with radius `1+‖Y‖` and taking the finite supremum over
all coordinates gives the stated inequality.

All factorization premises are explicit. This is the polynomial
geometric input for an archimedean Schwartz estimate, and does not
yet assert rapid decay of a gauge or Mellin integrability.
