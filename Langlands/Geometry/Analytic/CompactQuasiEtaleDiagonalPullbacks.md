# Compact site pullbacks from analytic-domain diagonals

For compact objects `U`, `V` and `B` of the quasi-étale site over a
Hausdorff analytic space `X`, take the full localized products of
`U` with `V` and of `B` with itself over `X`. The two arrows into `B`
induce a map from the first product into the second.

If the diagonal of `B` is an analytic-domain embedding in its
self-product, pull that domain back along the induced map. The
resulting inverse-image domain is the full pullback over `B`.
Indeed, the compatibility over `B` is exactly the condition that a
pair of maps into `U` and `V` lifts through the diagonal. The proof
checks this equality by composing with both projections of the
self-product.

The diagonal domain is compact by its isomorphism with `B`. It is
closed in the Hausdorff self-product, so its inverse image is compact
Hausdorff in the product of `U` and `V`. Under localized étale base
change, this product has local domain–étale factorizations over `X`.
Restricting these factorizations to the inverse-image domain gives
the quasi-étale structure map of the site pullback.

`CompactQuasiEtaleDiagonalDomainStatement` is the internal geometric
input for this construction. The theorem takes this input and
localized étale base change as hypotheses.
