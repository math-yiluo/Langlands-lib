# Actual products of full affinoid domains

This internal construction derives products of full represented domains from the published actual bounded affinoid coproduct, full-domain base change, intersections, and cancellation. It supports the product covering in Berkovich 1993, Lemma 1.2.12 (printed p.20 / PDF p.17), without claiming the source's descent or special-intersection theorem.

For full domains `U` of `A` and `V` of `B`, `U.product V` is the intersection of their inverse images along the two actual coproduct maps from `A` and `B`. It is therefore a full represented domain of `AffinoidCoproduct.algebra K A B`. Its locus is exactly the intersection of the two spectrum inverse images, with no claim that the spectrum of a coproduct is the set-theoretic product of spectra.

The two actual original domain algebras map into the product domain algebra through the base-change and intersection pushout legs. Their structural equations are proved. `productBaseMap` maps the ambient coproduct into the coproduct of the two unchanged domain algebras. The full universal property of that coproduct constructs `productCoproductMap` into the domain product algebra. Its composite with `productBaseMap` is the domain's actual structural map.

The spectrum image of `productBaseMap` belongs to the exact inverse-image intersection: the two coproduct leg equations reduce this assertion to the original domain image conditions. Full-domain representation then gives a bounded map in the reverse direction. Cancellation for the two original domain representations proves the two reverse leg identities. Coproduct uniqueness and cancellation for the product domain prove both inverse equations. `productCoproductEquiv` packages these actual bounded maps into an algebra equivalence with explicit forward and inverse norm bounds. No open mapping theorem or nontrivial coefficient valuation is used.

For two original inclusions, `productRestriction` is the full-domain inclusion on the literal product loci. Cancellation proves that its bounded restriction commutes with both unchanged domain-algebra maps.

All algebras retain actual closed finite positive-polyradius presentations, and every map is bounded with respect to its stored norm. The construction includes zero quotients, empty spectra, arbitrary positive radii, nonreduced algebras and trivial coefficient valuations. It supplies no quotient-effectiveness or atlas-intersection conclusion.
