# Finite product coverings by actual full domains

This internal construction uses `DomainProduct` and the existing finite-family cover constructor. It supplies the finite product covering used before ideal descent, without asserting any ideal-effectiveness or atlas-intersection result.

For actual finite full-domain covers `c` of `U` and `d` of `V`, `c.product d` has one member `(c.obj i).product (d.obj j)` for each pair of original indices. Its covering maps are the constructed product restrictions of `c.map i` and `d.map j`. A point in `U.product V` has first and second spectrum images in the two input loci. The two original covering conditions supply indices containing these images. The exact product-locus formula then puts the original point in their product component. This argument uses spectrum inverse images, rather than identifying the spectrum of a completed tensor product with a set-theoretic product.

The finite family is enumerated through `FiniteCover.ofFintype`. `productIndexEquiv` and `productIndex` retain the explicit relation to the two original index sets, and the component and arrow identities expose the exact choices. The size is the product of the input sizes.

For covers of the two whole spectra, `coproductCover` retains these same product members and constructs their actual full-domain inclusions into the whole ambient affinoid coproduct. The two whole-factor locus conditions hold for every ambient coproduct point, so the preceding product coverage proves coverage of that entire spectrum.

All bounded restrictions and positive-polyradius presentations are retained. Either cover can be empty; no nonempty spectrum, nonzero quotient, reducedness, strictness or nontrivial coefficient valuation is assumed. This is a direct internal consequence of the imported constructions, with no independent literature assertion.
