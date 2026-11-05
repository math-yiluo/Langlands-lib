# Transitivity of coefficient-point norms

This internal development proves the tower law for the actual coefficient norm
of an affine commutative group scheme over a field `k`.
For `k → L → M` with all relevant extensions finite Galois,
`norm_relativeNorm` states
`norm k L T (relativeNorm k L M T x) = norm k M T x`.
The point carriers all belong to the original group scheme over `k`.

The proof extends both sides to `M`, where extension is injective.
The extension of each norm is its product over field automorphisms.
`towerAutEquiv` parametrizes an automorphism of `M/k` uniquely as a chosen
lift of an `L/k` automorphism followed by an `M/L` automorphism. Injectivity
uses restriction to `L`; surjectivity divides by the chosen lift and regards
the remaining automorphism as an `L`-algebra automorphism. Coordinate
evaluation proves compatibility of extension with conjugation and with
the original base-field extension. Reindexing the double product gives
the full `M/k` product.

This is derived infrastructure for the splitting-field comparison in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 2.5.12 and Definition 2.5.13, printed pp.89–90 (PDF pp.120–121).
It proves the tower law only; it assumes no unit-norm surjectivity and
does not assert independence of the splitting field or of the zero subgroup.
