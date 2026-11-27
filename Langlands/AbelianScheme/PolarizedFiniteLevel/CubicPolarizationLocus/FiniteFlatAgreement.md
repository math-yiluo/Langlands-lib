# Closed agreement on a finite flat source

`exists_finiteFlat_agreement_locus` takes two maps over a locally noetherian scheme from a finite flat source to a separated target. It constructs a closed subscheme of the base whose factorization property is equality of the two maps on the whole pulled-back source.

Over an affine chart the coordinate module of the finite flat source is projective, since it is finite over a noetherian ring and flat. The closed factorization locus of the equalizer in the product with the identity test represents agreement there. Pullback associativity transports this criterion from affine spectra to affine opens. Equality of scheme maps is detected by the pulled-back open cover, so `closedLocusFromAffineCharts` gives the global closed subscheme. The factorization property includes nonreduced tests.

This is the finite flat coefficient argument in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), the proof of Proposition 6.11 on printed pp. 122–123 (PDF pp. 135–136). The registered source is `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`, SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
